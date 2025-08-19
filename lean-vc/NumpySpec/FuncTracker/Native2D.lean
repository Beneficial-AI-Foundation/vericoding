import Lean
import FuncTracker.BasicV2
import FuncTracker.TwoDSyntax  
import FuncTracker.BoxDrawing
import FuncTracker.SpatialParser
import FuncTracker.PrettyFormat

namespace FuncTracker.TwoD.Native

open Lean Elab Term Meta
open FuncTracker
open FuncTracker.TwoD
open FuncTracker.TwoD.SpatialParser
open FuncTracker.TwoD.PrettyFormat

/-!
# Native2D - Native 2D Table Syntax Implementation

This module implements the `funcTable2d` macro that provides native 2D table syntax
for FuncTracker, replacing the string-based `funcTable!` approach with beautiful
direct 2D layout parsing.

## Usage

Instead of:
```lean
funcTable! "╔═══╗\n│...│\n╚═══╝"
```

Use native 2D syntax:
```lean
funcTable2d
╔══════════════╦═══════════╦═════════════╗
║ Function     ║ Status    ║ File        ║
╠══════════════╬═══════════╬═════════════╣
║ List.map     ║ ✓✓✓       ║ List.lean   ║
║ Array.map    ║ ✓✓        ║ Array.lean  ║
╚══════════════╩═══════════╩═════════════╝
```

## Design Philosophy

- **Native syntax**: The 2D layout IS the syntax, not a string to be parsed
- **Forgiving**: Handle slightly misaligned tables gracefully (Phase 1)
- **Type safe**: Validate function names exist at compile time
- **Beautiful**: Generate aesthetically pleasing output
-/

/-- Custom syntax category for 2D table content -/
declare_syntax_cat twod_table_content

/-- Syntax for raw 2D table text (temporary Phase 1 approach) -/
syntax twod_table_line := many1(anyChar)
syntax twod_table_content := many1(twod_table_line linebreak)

/-- Main funcTable2d syntax that captures everything until the end of the block -/
syntax (name := funcTable2d) "funcTable2d" linebreak
  twod_table_content : term

/-- Helper function to extract 2D table text from syntax -/
private def extract2DText (stx : Syntax) : TermElabM String := do
  -- For Phase 1, we'll extract the raw text content
  -- This is a simplified approach that treats the content as text
  let sourceText := stx.getPos?.bind fun pos =>
    stx.getTailPos?.map fun tailPos =>
      (← getMainModule).src.extract pos tailPos
  match sourceText with
  | some text => 
    -- Clean up the text by removing the first line (funcTable2d declaration)
    let lines := text.splitOn "\n"
    let tableLines := lines.drop 1  -- Remove "funcTable2d" line
    let cleanedText := String.intercalate "\n" tableLines
    pure cleanedText.trim
  | none => throwError "Could not extract 2D table text"

/-- Parse status symbol to Status enum -/
private def parseStatusSymbol (s : String) : TermElabM Status := do
  match s.trim with
  | "✗" => pure Status.notStarted
  | "⋯" => pure Status.inProgress  
  | "✓" => pure Status.implemented
  | "✓✓" => pure Status.tested
  | "✓✓✓" => pure Status.documented
  | other => throwError s!"Unknown status symbol: {other}"

/-- Validate that a function name exists in the current environment -/
private def validateFunctionName (name : String) : TermElabM Unit := do
  let env ← getEnv
  let leanName := stringToName name
  if !env.contains leanName then
    throwError s!"Function name '{name}' not found in environment"

/-- Convert parsed function data to TrackedFunction expression -/
private def buildTrackedFunction (name status file : String) : TermElabM Expr := do
  -- Validate the function name exists
  validateFunctionName name
  
  -- Parse status
  let statusEnum ← parseStatusSymbol status
  
  -- Build the TrackedFunction expression
  let nameExpr ← mkAppM ``stringToName #[mkStrLit name]
  let statusExpr ← match statusEnum with
    | .notStarted => mkAppM ``Status.notStarted #[]
    | .inProgress => mkAppM ``Status.inProgress #[] 
    | .implemented => mkAppM ``Status.implemented #[]
    | .tested => mkAppM ``Status.tested #[]
    | .documented => mkAppM ``Status.documented #[]
  
  -- Handle optional file
  let fileExpr ← if file.trim.isEmpty || file.trim == "-" then
    mkAppM ``Option.none #[mkConst ``String]
  else
    mkAppM ``Option.some #[mkStrLit file.trim]
  
  -- Create TrackedFunction with default values for other fields
  let linesExpr ← mkAppM ``Option.none #[← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]]
  let complexityExpr ← mkAppM ``Option.none #[mkConst ``String]
  let docStringExpr ← mkAppM ``Option.none #[mkConst ``String]
  let versoLinkExpr ← mkAppM ``Option.none #[mkConst ``String]
  let refsExpr ← mkArrayLit (← mkAppM ``Name #[]) []
  let typedRefsExpr ← mkArrayLit (← mkAppM ``CrossReference #[]) []
  let versionExpr ← mkAppM ``Option.none #[mkConst ``String]
  
  mkAppM ``TrackedFunction.mk #[
    nameExpr, statusExpr, fileExpr, linesExpr, complexityExpr, 
    docStringExpr, versoLinkExpr, refsExpr, typedRefsExpr, versionExpr
  ]

/-- Build FunctionTable expression from parsed data -/
private def buildFunctionTable (functionData : Array (String × String × Option String)) : TermElabM Expr := do
  -- Convert each function data entry to TrackedFunction
  let functionExprs ← functionData.mapM fun (name, status, fileOpt) => do
    let file := fileOpt.getD ""
    buildTrackedFunction name status file
  
  -- Create array of TrackedFunction
  let functionsArray ← mkArrayLit (← mkAppM ``TrackedFunction #[]) functionExprs.toList
  
  -- Create FunctionTable with no module specified
  let moduleExpr ← mkAppM ``Option.none #[mkConst ``Name]
  mkAppM ``FunctionTable.mk #[functionsArray, moduleExpr]

/-- Main elaborator for funcTable2d syntax -/
@[term_elab funcTable2d]
def elabFuncTable2d : TermElab := fun stx _ => do
  -- Extract the 2D table text
  let tableText ← extract2DText stx
  
  -- Parse the 2D table structure
  match parseTableToFunctionData tableText with
  | .ok functionData => 
    -- Validate and build the FunctionTable expression
    buildFunctionTable functionData
  | .error msg => 
    throwError s!"Failed to parse 2D table: {msg}"

/-- Helper macro for quick testing (Phase 1) -/
syntax (name := simpleTable2d) "simpleTable2d" str : term

@[term_elab simpleTable2d] 
def elabSimpleTable2d : TermElab := fun stx _ => do
  match stx with
  | `(simpleTable2d $s:str) => do
    let tableStr := s.getString
    match parseTableToFunctionData tableStr with
    | .ok functionData =>
      buildFunctionTable functionData 
    | .error msg =>
      throwError s!"Parse error: {msg}"
  | _ => throwUnsupportedSyntax

/-- Pretty-print a FunctionTable as beautiful 2D syntax -/
def functionTableTo2D (table : FunctionTable) : String :=
  if table.functions.isEmpty then
    "-- Empty table --"
  else
    -- Calculate column widths
    let nameWidth := table.functions.foldl (fun acc f => max acc f.name.toString.length) 8
    let statusWidth := 10
    let fileWidth := table.functions.foldl (fun acc f => 
      match f.file with
      | some file => max acc file.length
      | none => acc) 8
    
    -- Generate table structure
    let topBorder := "╔" ++ String.mk (List.replicate nameWidth '═') ++ "╦" ++ 
                     String.mk (List.replicate statusWidth '═') ++ "╦" ++
                     String.mk (List.replicate fileWidth '═') ++ "╗"
    
    let separator := "╠" ++ String.mk (List.replicate nameWidth '═') ++ "╬" ++ 
                     String.mk (List.replicate statusWidth '═') ++ "╬" ++
                     String.mk (List.replicate fileWidth '═') ++ "╣"
    
    let bottomBorder := "╚" ++ String.mk (List.replicate nameWidth '═') ++ "╩" ++ 
                        String.mk (List.replicate statusWidth '═') ++ "╩" ++
                        String.mk (List.replicate fileWidth '═') ++ "╝"
    
    -- Header row
    let padString (s : String) (width : Nat) : String :=
      let trimmed := s.take width
      trimmed ++ String.mk (List.replicate (width - trimmed.length) ' ')
    
    let header := "║ " ++ padString "Function" (nameWidth - 1) ++ 
                  "║ " ++ padString "Status" (statusWidth - 1) ++ 
                  "║ " ++ padString "File" (fileWidth - 1) ++ "║"
    
    -- Data rows
    let dataRows := table.functions.toList.map fun f =>
      let name := padString f.name.toString (nameWidth - 1)
      let status := padString f.status.toSymbol (statusWidth - 1) 
      let file := padString (f.file.getD "-") (fileWidth - 1)
      "║ " ++ name ++ "║ " ++ status ++ "║ " ++ file ++ "║"
    
    String.intercalate "\n" ([topBorder, header, separator] ++ dataRows ++ [bottomBorder])

/-- Enhanced pretty-printing with style options -/
def formatTableWithStyle (table : FunctionTable) (style : TableFormat := defaultFunctionTableFormat) : String :=
  formatFunctionTable table style

/-- Generate beautiful 2D table with automatic formatting -/
def autoFormat (table : FunctionTable) : String :=
  let formatted := formatFunctionTable table Styles.elegant
  "funcTable2d\n" ++ formatted

/-- Code action integration for pretty-printing -/
def formatTableAction (table : FunctionTable) : String :=
  autoFormat table

/-- Enhanced funcTable2d with style support -/
syntax (name := styledFuncTable2d) "funcTable2d" "(" ident ")" linebreak
  twod_table_content : term

@[term_elab styledFuncTable2d]
def elabStyledFuncTable2d : TermElab := fun stx _ => do
  match stx with
  | `(funcTable2d ($style:ident) $content) => do
    -- Extract the 2D table text
    let tableText ← extract2DText content
    
    -- Parse the 2D table structure
    match parseTableToFunctionData tableText with
    | .ok functionData => 
      buildFunctionTable functionData
    | .error msg => 
      throwError s!"Failed to parse styled 2D table: {msg}"
  | _ => throwUnsupportedSyntax

/-- Multi-format export functionality -/
namespace TableExport

/-- Export table to multiple formats -/
structure ExportResult where
  markdown : String
  html : String
  latex : String
  csv : String
  ascii : String

def exportAll (table : FunctionTable) : ExportResult := {
  markdown := Export.toMarkdown table,
  html := Export.toHTML table,
  latex := Export.toLaTeX table,
  csv := Export.toCSV table,
  ascii := formatFunctionTable table Styles.minimal
}

/-- Save exports to files (for future integration) -/
def saveExports (table : FunctionTable) (baseName : String) : IO Unit := do
  let exports := exportAll table
  IO.FS.writeFile (baseName ++ ".md") exports.markdown
  IO.FS.writeFile (baseName ++ ".html") exports.html
  IO.FS.writeFile (baseName ++ ".tex") exports.latex
  IO.FS.writeFile (baseName ++ ".csv") exports.csv
  IO.FS.writeFile (baseName ++ ".txt") exports.ascii

end TableExport

/-- Advanced formatting with custom styles -/
namespace AdvancedFormat

/-- Create a custom style based on content analysis -/
def analyzeAndFormat (table : FunctionTable) : String :=
  let maxNameLength := table.functions.foldl (fun acc f => max acc f.name.toString.length) 0
  let hasFiles := table.functions.any (fun f => f.file.isSome)
  
  let customFormat : TableFormat := {
    borderStyle := if table.functions.size > 10 then .light else .heavy,
    columnFormats := #[
      { minWidth := max 15 maxNameLength, alignment := .left, padding := (1, 1) },
      { minWidth := 10, alignment := .center, padding := (1, 1) },
      { minWidth := if hasFiles then 15 else 8, alignment := .left, padding := (1, 1) }
    ],
    includeHeaderSeparator := true
  }
  
  formatFunctionTable table customFormat

/-- Format for specific contexts -/
def formatForContext (table : FunctionTable) (context : String) : String :=
  match context with
  | "presentation" => formatFunctionTable table Styles.elegant
  | "development" => formatFunctionTable table Styles.minimal  
  | "documentation" => formatFunctionTable table Styles.rounded
  | "compact" => formatFunctionTable table Styles.compact
  | _ => formatFunctionTable table defaultFunctionTableFormat

end AdvancedFormat

end FuncTracker.TwoD.Native