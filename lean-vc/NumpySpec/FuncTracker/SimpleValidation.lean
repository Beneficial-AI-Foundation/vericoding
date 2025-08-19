import Lean
import FuncTracker.BasicV2
import FuncTracker.GridParserV2

namespace FuncTracker

open Lean Elab Term Meta

/-- Define the syntax for funcTable! with validation -/
syntax (name := funcTableValidated) "funcTable!" str : term

/-- Elaborate a function table with validation -/
@[term_elab funcTableValidated]
def elabFuncTableValidated : TermElab := fun stx _ => do
  match stx with
  | `(funcTable! $s:str) => do
    let tableStr := s.getString
    
    -- Parse the table
    let grid ← match GridParser.run tableStr with
      | .ok grid => pure grid
      | .error msg => throwError "Parse error: {msg}"
    
    -- Remove header if present
    let dataGrid := 
      if grid.rows > 0 && grid.cells[0]!.any (fun cell => 
        cell ∈ ["Function", "Name", "Status", "File", "Lines", "Complexity", "Refs"]) then
        { cells := grid.cells[1:grid.cells.size], rows := grid.rows - 1, cols := grid.cols : Grid }
      else
        grid
    
    -- Convert to FunctionTable
    let table ← match gridToFunctionTableV2 dataGrid with
      | .ok table => pure table
      | .error msg => throwError "Conversion error: {msg}"
    
    -- Check each name exists
    let env ← getEnv
    for f in table.functions do
      if !env.contains f.name then
        throwError s!"Unknown identifier: {f.name}"
    
    -- Build expression (simplified)
    let functions ← table.functions.mapM fun f => do
      let name ← mkAppM ``stringToName #[mkStrLit f.name.toString]
      let status ← match f.status with
        | .notStarted => mkAppM ``Status.notStarted #[]
        | .inProgress => mkAppM ``Status.inProgress #[]
        | .implemented => mkAppM ``Status.implemented #[]
        | .tested => mkAppM ``Status.tested #[]
        | .documented => mkAppM ``Status.documented #[]
      let file ← mkAppOptM ``Option.none #[mkConst ``String]
      let lines ← mkAppOptM ``Option.none #[← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]]
      let complexity ← mkAppOptM ``Option.none #[mkConst ``String]
      let docString ← mkAppOptM ``Option.none #[mkConst ``String]
      let refs ← mkArrayLit (← mkAppM ``Name #[]) []
      mkAppM ``TrackedFunction.mk #[name, status, file, lines, complexity, docString, refs]
    
    let functionsArray ← mkArrayLit (← mkAppM ``TrackedFunction #[]) functions.toList
    let noneModule ← mkAppOptM ``Option.none #[mkConst ``Name]
    mkAppM ``FunctionTable.mk #[functionsArray, noneModule]
    
  | _ => throwUnsupportedSyntax

end FuncTracker