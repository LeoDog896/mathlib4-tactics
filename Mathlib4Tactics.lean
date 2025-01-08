import Mathlib.Tactic
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

open Lean Meta Elab Tactic Command

-- Avoids using Batteries.Tactic.OpenPrivate. Copied from Batteries/Tactic/HelpCmd.lean
def elabHelpCatCustom (more : Option Syntax) (catStx : Ident) (id : Option String) :
    CommandElabM Unit := do
  let mut decls : Lean.RBMap _ _ compare := {}
  let mut rest : Lean.RBMap _ _ compare := {}
  let catName := catStx.getId.eraseMacroScopes
  let some cat := (Parser.parserExtension.getState (← getEnv)).categories.find? catName
    | throwErrorAt catStx "{catStx} is not a syntax category"
  liftTermElabM <| Term.addCategoryInfo catStx catName
  let env ← getEnv
  for (k, _) in cat.kinds do
    let mut used := false
    if let some tk := do Batteries.Tactic.getHeadTk (← (← env.find? k).value?) then
      let tk := tk.trim
      if let some id := id then
        if !id.isPrefixOf tk then
          continue
      used := true
      decls := decls.insert tk ((decls.findD tk #[]).push k)
    if !used && id.isNone then
      rest := rest.insert (k.toString false) k
  let mut msg := MessageData.nil
  if decls.isEmpty && rest.isEmpty then
    match id with
    | some id => throwError "no {catName} declarations start with {id}"
    | none => throwError "no {catName} declarations found"
  let env ← getEnv
  let addMsg (k : SyntaxNodeKind) (msg msg1 : MessageData) : CommandElabM MessageData := do
    let mut msg1 := msg1
    if let some doc ← findDocString? env k then
      msg1 := msg1 ++ Format.line ++ doc.trim
    -- msg1 := .nest 2 msg1 -- don't nest this!
    if more.isSome then
      let addElabs {α} (type : String) (attr : KeyedDeclsAttribute α)
          (msg : MessageData) : CommandElabM MessageData := do
        let mut msg := msg
        for e in attr.getEntries env k do
          let x := e.declName
          msg := msg ++ Format.line ++ m!"+ {type} {mkConst x}"
          if let some doc ← findDocString? env x then
            msg := msg ++ .nest 2 (Format.line ++ doc.trim)
        pure msg
      msg1 ← addElabs "macro" macroAttribute msg1
      match catName with
      | `term => msg1 ← addElabs "term elab" Term.termElabAttribute msg1
      | `command => msg1 ← addElabs "command elab" commandElabAttribute msg1
      | `tactic | `conv => msg1 ← addElabs "tactic elab" tacticElabAttribute msg1
      | _ => pure ()
    return msg ++ msg1 ++ (.line ++ .line : Format)
  for (name, ks) in decls do
    for k in ks do
      let identifierPoint := mkConst k
      let searchBase := "https://leanprover-community.github.io/mathlib4_docs/search.html?q="
      msg ← addMsg k msg m!"# {repr name} ({identifierPoint})[{searchBase}{identifierPoint}]\n"
  for (_, k) in rest do
    msg ← addMsg k msg m!"# [{mkConst k}]\n"
  logInfo msg

#eval Lean.logInfo "⊹---------------------⊹"
#eval elabHelpCatCustom none (Lean.mkIdent `tactic) none
#eval Lean.logInfo "⊹---------------------⊹"
