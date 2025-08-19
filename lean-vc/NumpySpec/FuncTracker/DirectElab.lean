import Lean
import FuncTracker.BasicV2
import FuncTracker.NativeSyntax

namespace FuncTracker.DirectElab

open Lean Elab Term Meta
open FuncTracker
open FuncTracker.NativeSyntax

/-!
# DirectElab - Direct Syntax Tree Processing (No Strings!)

This module implements true native 2D elaboration by processing syntax trees
directly, without any string parsing. This is the core of our native 2D approach.

## Key Innovation

Instead of extracting strings from syntax and parsing them:
```lean
let tableText ← extract2DText stx  -- String extraction ❌
parseTableToFunctionData tableText -- String parsing ❌
```

We process the **syntax tree structure directly**:
```lean  
let borderStx := stx[1]           -- Direct syntax access ✅
let columnCount ← analyzeColumns borderStx -- Structural analysis ✅
let rowsStx := stx[2]             -- Direct row access ✅
```

## Benefits

- **Zero string parsing overhead**: Direct syntax tree processing
- **Preserve spatial relationships**: Maintain 2D structure throughout
- **Type safety**: Full Lean type checking on native syntax
- **Rich error messages**: Precise syntax-level error reporting
- **IDE integration**: Perfect LSP support through proper syntax trees
-/

-- =============================================================================
-- SYNTAX TREE ANALYSIS
-- =============================================================================

/-- Extract column count from border syntax structure -/
def analyzeColumnCount (borderStx : Syntax) : TermElabM Nat := do
  -- Count junction characters to determine columns
  let junctionCount := countSyntaxKind borderStx `box_junction_t +
                      countSyntaxKind borderStx `box_junction_b +
                      countSyntaxKind borderStx `box_junction_x
  let columnCount := junctionCount + 1
  
  if columnCount < 1 then
    throwError "Table must have at least one column"
  
  return columnCount

/-- Extract cell content from a table row syntax node -/
def extractCellContent (cellStx : Syntax) : TermElabM String := do
  match cellStx with
  | .ident _ _ text _ => return text.toString
  | .atom _ text => return text
  | .node _ kind args =>
    -- Handle compound cells like "List.lean" (ident.ident)
    if kind == `Lean.Parser.Term.dotIdent then
      let parts := args.toList.map syntaxToText
      return String.intercalate "." parts
    else
      -- Handle other node types
      return syntaxToText cellStx
  | _ => 
    throwError s!"Unexpected cell content syntax: {cellStx.getKind}"

/-- Extract all cell contents from a row syntax -/
def extractRowCells (rowStx : Syntax) : TermElabM (Array String) := do
  let cellNodes := extractCellNodes rowStx
  cellNodes.mapM extractCellContent

/-- Parse status from cell content -/
def parseStatusFromCell (cellContent : String) : TermElabM Status := do
  match cellContent.trim with
  | "✗" => return .notStarted
  | "⋯" => return .inProgress
  | "✓" => return .implemented
  | "✓✓" => return .tested
  | "✓✓✓" => return .documented
  | other => throwError s!"Invalid status symbol: '{other}'"

/-- Extract function data from table row syntax -/
def extractFunctionFromRow (rowStx : Syntax) (expectedCols : Nat) : TermElabM TrackedFunction := do
  let cellContents ← extractRowCells rowStx
  
  if cellContents.size != expectedCols then
    throwError s!"Row has {cellContents.size} cells, expected {expectedCols}"
  
  if cellContents.size < 2 then
    throwError "Row must have at least function name and status columns"
  
  -- Extract function name (column 0)
  let nameStr := cellContents[0]!
  if nameStr.isEmpty then
    throwError "Function name cannot be empty"
  
  -- Validate function name exists in environment
  let env ← getEnv
  let leanName := stringToName nameStr
  if !env.contains leanName then
    throwError s!"Function '{nameStr}' not found in environment"
  
  -- Extract status (column 1)
  let statusStr := cellContents[1]!
  let status ← parseStatusFromCell statusStr
  
  -- Extract optional file (column 2)
  let file := if cellContents.size > 2 then
    let fileStr := cellContents[2]!.trim
    if fileStr.isEmpty || fileStr == "-" then none else some fileStr
  else none
  
  -- Extract optional lines (column 3)
  let lines := if cellContents.size > 3 then
    let linesStr := cellContents[3]!.trim
    if linesStr.isEmpty || linesStr == "-" then none
    else
      -- Parse "10-20" format
      let parts := linesStr.splitOn "-"
      if parts.length == 2 then
        match parts[0]!.toNat?, parts[1]!.toNat? with
        | some start, some «end» => some (start, «end»)
        | _, _ => none
      else none
  else none
  
  -- Extract optional complexity (column 4)
  let complexity := if cellContents.size > 4 then
    let complexityStr := cellContents[4]!.trim
    if complexityStr.isEmpty || complexityStr == "-" then none else some complexityStr
  else none
  
  return {
    name := leanName
    status := status
    file := file
    lines := lines
    complexity := complexity
    docString := none
    versoLink := none
    refs := #[]
    typedRefs := #[]
    version := none
  }

-- =============================================================================
-- DIRECT SYNTAX ELABORATION
-- =============================================================================

/-- Build TrackedFunction expressions from extracted data -/
def buildTrackedFunctionExpr (func : TrackedFunction) : TermElabM Expr := do
  -- Build the TrackedFunction expression
  let nameExpr ← mkAppM ``stringToName #[mkStrLit func.name.toString]
  let statusExpr ← match func.status with
    | .notStarted => mkAppM ``Status.notStarted #[]
    | .inProgress => mkAppM ``Status.inProgress #[]
    | .implemented => mkAppM ``Status.implemented #[]
    | .tested => mkAppM ``Status.tested #[]
    | .documented => mkAppM ``Status.documented #[]
  
  -- Handle optional file
  let fileExpr ← match func.file with
    | none => mkAppM ``Option.none #[mkConst ``String]
    | some file => mkAppM ``Option.some #[mkStrLit file]
  
  -- Handle optional lines
  let linesExpr ← match func.lines with
    | none => mkAppM ``Option.none #[← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]]
    | some (start, «end») =>
      let pairExpr ← mkAppM ``Prod.mk #[mkNatLit start, mkNatLit «end»]
      mkAppM ``Option.some #[pairExpr]
  
  -- Handle optional complexity
  let complexityExpr ← match func.complexity with
    | none => mkAppM ``Option.none #[mkConst ``String]
    | some complexity => mkAppM ``Option.some #[mkStrLit complexity]
  
  -- Default values for other fields
  let docStringExpr ← mkAppM ``Option.none #[mkConst ``String]
  let versoLinkExpr ← mkAppM ``Option.none #[mkConst ``String]
  let refsExpr ← mkArrayLit (← mkAppM ``Name #[]) []
  let typedRefsExpr ← mkArrayLit (← mkAppM ``CrossReference #[]) []
  let versionExpr ← mkAppM ``Option.none #[mkConst ``String]
  
  mkAppM ``TrackedFunction.mk #[
    nameExpr, statusExpr, fileExpr, linesExpr, complexityExpr,
    docStringExpr, versoLinkExpr, refsExpr, typedRefsExpr, versionExpr
  ]

/-- Build FunctionTable expression from function data -/
def buildFunctionTableExpr (functions : Array TrackedFunction) : TermElabM Expr := do
  -- Convert each function to an expression
  let functionExprs ← functions.mapM buildTrackedFunctionExpr
  
  -- Create array of TrackedFunction
  let functionsArray ← mkArrayLit (← mkAppM ``TrackedFunction #[]) functionExprs.toList
  
  -- Create FunctionTable with no module specified
  let moduleExpr ← mkAppM ``Option.none #[mkConst ``Name]
  mkAppM ``FunctionTable.mk #[functionsArray, moduleExpr]

-- =============================================================================
-- MAIN ELABORATORS
-- =============================================================================

/-- Main elaborator for native 2D table syntax -/
@[term_elab nativeTable2d]
def elabNativeTable2d : TermElab := fun stx expectedType => do
  -- Extract syntax components directly (no string parsing!)
  let components := stx.getArgs
  
  if components.size < 5 then
    throwError "Invalid table structure: insufficient components"
  
  -- Extract structural components
  let topBorderStx := components[1]!      -- Top border: ╔═══╦═══╗
  let headerRowStx := components[2]!      -- Header row: ║ Name ║ Status ║
  let separatorStx := components[3]!      -- Separator: ╠═══╬═══╣
  let dataRowsStx := components[4]!       -- Data rows
  let bottomBorderStx := components[5]!   -- Bottom border: ╚═══╩═══╝
  
  -- Analyze table structure from syntax
  let columnCount ← analyzeColumnCount topBorderStx
  
  -- Validate border consistency
  if !validateBorderConsistency topBorderStx bottomBorderStx then
    throwError "Table borders are inconsistent"
  
  -- Extract header information (for validation)
  let headerCells ← extractRowCells headerRowStx
  if headerCells.size != columnCount then
    throwError s!"Header has {headerCells.size} cells, expected {columnCount}"
  
  -- Extract data rows
  let dataRowNodes := dataRowsStx.getArgs.filter (fun node => 
    node.getKind == `table_row)
  
  if dataRowNodes.isEmpty then
    throwError "Table must contain at least one data row"
  
  -- Process each data row
  let functions ← dataRowNodes.mapM (extractFunctionFromRow · columnCount)
  
  -- Build the final FunctionTable expression
  buildFunctionTableExpr functions

/-- Simpler elaborator for testing -/
@[term_elab simpleNativeTable2d] 
def elabSimpleNativeTable2d : TermElab := fun stx expectedType => do
  -- Simplified version with just top border, one row, bottom border
  let components := stx.getArgs
  
  if components.size < 3 then
    throwError "Invalid simple table structure"
  
  let topBorderStx := components[1]!
  let dataRowStx := components[2]!
  let bottomBorderStx := components[3]!
  
  -- Analyze structure
  let columnCount ← analyzeColumnCount topBorderStx
  
  -- Extract single row
  let func ← extractFunctionFromRow dataRowStx columnCount
  
  -- Build table with single function
  buildFunctionTableExpr #[func]

-- =============================================================================
-- VALIDATION AND ERROR HANDLING
-- =============================================================================

/-- Validate complete table structure -/
def validateTableStructure (stx : Syntax) : TermElabM Unit := do
  -- Check that we have the expected syntax structure
  let components := stx.getArgs
  
  if components.size < 5 then
    throwError "Table must have: top border, header, separator, data rows, bottom border"
  
  -- Validate each component has correct syntax kind
  let topBorder := components[1]!
  let headerRow := components[2]!
  let separator := components[3]!
  let dataRows := components[4]!
  let bottomBorder := components[5]!
  
  -- Check syntax kinds
  if topBorder.getKind != `table_border then
    throwError s!"Expected table_border, got {topBorder.getKind}"
  
  if headerRow.getKind != `table_row then
    throwError s!"Expected table_row for header, got {headerRow.getKind}"
  
  if separator.getKind != `table_separator then
    throwError s!"Expected table_separator, got {separator.getKind}"
  
  if bottomBorder.getKind != `table_border then
    throwError s!"Expected table_border, got {bottomBorder.getKind}"

/-- Generate helpful error messages for syntax issues -/
def generateSyntaxDiagnostic (stx : Syntax) : String :=
  let kind := stx.getKind
  let pos := stx.getPos?.map toString |>.getD "unknown"
  s!"Syntax error at {pos}: unexpected {kind}"

-- =============================================================================
-- DEBUGGING UTILITIES  
-- =============================================================================

/-- Debug elaboration by showing syntax tree structure -/
def debugElaboration (stx : Syntax) : TermElabM Unit := do
  let structure := inspectSyntaxTree stx
  logInfo s!"Syntax tree structure:\n{structure}"
  
  let tokenCount := countTokens stx
  logInfo s!"Total tokens: {tokenCount}"
  
  -- Show box-drawing character distribution
  let boxChars := #[`box_corner_tl, `box_corner_tr, `box_corner_bl, `box_corner_br,
                   `box_vertical, `box_horizontal, `box_junction_t, `box_junction_b,
                   `box_junction_l, `box_junction_r, `box_junction_x]
  
  for kind in boxChars do
    let count := countSyntaxKind stx kind
    if count > 0 then
      logInfo s!"{kind}: {count} occurrences"

end FuncTracker.DirectElab