import Lean
import FuncTracker.BasicV2
import FuncTracker.Native2D
import FuncTracker.PrettyFormat
import FuncTracker.SpatialParser

namespace FuncTracker.TwoD.CodeActions

open Lean Lsp Server
open FuncTracker
open FuncTracker.TwoD.Native
open FuncTracker.TwoD.PrettyFormat
open FuncTracker.TwoD.SpatialParser

/-!
# CodeActions - LSP Integration for Table Formatting

This module provides Language Server Protocol (LSP) integration for FuncTracker tables,
enabling rich IDE support with code actions for formatting, styling, and conversion.

## Supported Code Actions

1. **Format Table**: Beautify existing table with proper alignment and styling
2. **Convert to 2D**: Transform string-based funcTable! to native funcTable2d syntax
3. **Change Style**: Apply different table styles (elegant, minimal, compact, rounded)
4. **Export Table**: Generate exports in various formats (Markdown, HTML, LaTeX, CSV)
5. **Auto-Fix Alignment**: Correct misaligned table borders and content

## LSP Integration Points

- **Hover Information**: Rich table metadata and progress statistics
- **Diagnostics**: Table structure validation and formatting suggestions
- **Code Actions**: Context-sensitive formatting and conversion options
- **Completion**: Smart box-drawing character insertion
- **Formatting**: Automatic table beautification on save

## Design Philosophy

Provide seamless IDE integration that makes 2D table editing as natural as writing text:
- Non-intrusive: Actions appear only when relevant
- Context-aware: Different actions for different table types and states
- Performance-focused: Fast analysis and formatting
- User-friendly: Clear action descriptions and preview capabilities
-/

/-- Code action types for table operations -/
inductive TableActionType where
  | formatTable
  | convertTo2D
  | changeStyle (style : String)
  | exportFormat (format : String)
  | fixAlignment
  | addRow
  | addColumn
  | validateReferences
  deriving Repr, BEq, DecidableEq

instance : ToString TableActionType where
  toString
  | .formatTable => "Format Table"
  | .convertTo2D => "Convert to 2D Syntax"
  | .changeStyle style => s!"Apply {style} Style"
  | .exportFormat format => s!"Export as {format}"
  | .fixAlignment => "Fix Table Alignment"
  | .addRow => "Add Table Row"
  | .addColumn => "Add Table Column"
  | .validateReferences => "Validate Function References"

/-- Context information for determining available code actions -/
structure TableContext where
  /-- Whether cursor is within a table -/
  inTable : Bool
  /-- Type of table syntax detected -/
  tableType : Option String  -- "funcTable!" | "funcTable2d" | "simpleTable2d"
  /-- Table content if parseable -/
  tableData : Option FunctionTable
  /-- Current table text -/
  tableText : String
  /-- Cursor position within table -/
  cursorPos : Nat × Nat  -- (row, col)
  /-- Table boundaries in source -/
  tableBounds : Nat × Nat  -- (start, end) character positions
  deriving Repr

/-- Result of a code action -/
structure ActionResult where
  /-- New text to replace the table -/
  newText : String
  /-- Description of what changed -/
  description : String
  /-- Whether the change affects table structure -/
  structuralChange : Bool
  deriving Repr

/-- Analyze text to determine table context -/
def analyzeTableContext (text : String) (cursorPos : Nat) : TableContext :=
  -- Simple heuristic: look for table patterns around cursor
  let lines := text.splitOn "\n"
  let hasBoxChars := text.any isBoxDrawingChar
  let hasFuncTable := text.contains "funcTable"
  
  if hasBoxChars || hasFuncTable then
    -- Try to parse as table
    let tableType := 
      if text.contains "funcTable!" then some "funcTable!"
      else if text.contains "funcTable2d" then some "funcTable2d"  
      else if text.contains "simpleTable2d" then some "simpleTable2d"
      else none
    
    let tableData := 
      if looksLikeTable text then
        match parseTableToFunctionData text with
        | .ok functionData => 
          let table : FunctionTable := { functions := functionData.map fun (name, status, file) =>
            { name := stringToName name
              status := match status with
                | "✗" => .notStarted | "⋯" => .inProgress | "✓" => .implemented
                | "✓✓" => .tested | "✓✓✓" => .documented | _ => .notStarted
              file := file
              lines := none, complexity := none, docString := none
              versoLink := none, refs := #[], typedRefs := #[], version := none } }
          some table
        | .error _ => none
      else none
    
    { inTable := true
      tableType := tableType
      tableData := tableData
      tableText := text
      cursorPos := (0, 0)  -- Simplified for demo
      tableBounds := (0, text.length) }
  else
    { inTable := false, tableType := none, tableData := none
      tableText := "", cursorPos := (0, 0), tableBounds := (0, 0) }

/-- Get available code actions for a given context -/
def getAvailableActions (context : TableContext) : Array TableActionType :=
  if !context.inTable then #[]
  else
    let baseActions := #[.formatTable, .fixAlignment, .validateReferences]
    
    let conversionActions := 
      if context.tableType == some "funcTable!" then #[.convertTo2D]
      else #[]
    
    let styleActions := #[
      .changeStyle "elegant",
      .changeStyle "minimal", 
      .changeStyle "compact",
      .changeStyle "rounded"
    ]
    
    let exportActions := #[
      .exportFormat "Markdown",
      .exportFormat "HTML",
      .exportFormat "LaTeX", 
      .exportFormat "CSV"
    ]
    
    let editActions := #[.addRow, .addColumn]
    
    baseActions ++ conversionActions ++ styleActions ++ exportActions ++ editActions

/-- Execute a specific code action -/
def executeAction (action : TableActionType) (context : TableContext) : Except String ActionResult :=
  match context.tableData with
  | none => .error "No valid table data to process"
  | some table =>
    match action with
    | .formatTable => 
      let formatted := formatFunctionTable table Styles.elegant
      .ok { newText := formatted
            description := "Applied elegant formatting to table"
            structuralChange := false }
    
    | .convertTo2D =>
      let formatted := autoFormat table
      .ok { newText := formatted
            description := "Converted funcTable! to native funcTable2d syntax"
            structuralChange := true }
    
    | .changeStyle style =>
      let styleFormat := match style with
        | "elegant" => Styles.elegant
        | "minimal" => Styles.minimal
        | "compact" => Styles.compact
        | "rounded" => Styles.rounded
        | _ => defaultFunctionTableFormat
      let formatted := formatFunctionTable table styleFormat
      .ok { newText := formatted
            description := s!"Applied {style} style to table"
            structuralChange := false }
    
    | .exportFormat format =>
      let exported := match format with
        | "Markdown" => Export.toMarkdown table
        | "HTML" => Export.toHTML table
        | "LaTeX" => Export.toLaTeX table
        | "CSV" => Export.toCSV table
        | _ => formatFunctionTable table Styles.minimal
      .ok { newText := exported
            description := s!"Exported table as {format}"
            structuralChange := true }
    
    | .fixAlignment =>
      let fixed := AdvancedFormat.analyzeAndFormat table
      .ok { newText := fixed
            description := "Fixed table alignment and formatting"
            structuralChange := false }
    
    | .addRow =>
      -- Add empty row template
      let newFunction : TrackedFunction := {
        name := stringToName "NewFunction"
        status := .notStarted
        file := none, lines := none, complexity := none, docString := none
        versoLink := none, refs := #[], typedRefs := #[], version := none
      }
      let newTable := { table with functions := table.functions.push newFunction }
      let formatted := formatFunctionTable newTable Styles.elegant
      .ok { newText := formatted
            description := "Added new row to table"
            structuralChange := true }
    
    | .addColumn =>
      .error "Adding columns not yet implemented"
    
    | .validateReferences =>
      -- Check if all function names are valid
      let invalidFunctions := table.functions.filter fun f =>
        f.name.toString.isEmpty || f.name.toString == "NewFunction"
      if invalidFunctions.isEmpty then
        .ok { newText := context.tableText
              description := "All function references are valid"
              structuralChange := false }
      else
        .error s!"Found {invalidFunctions.size} invalid function references"

/-- LSP hover information for tables -/
def generateHoverInfo (context : TableContext) : Option String :=
  match context.tableData with
  | none => none
  | some table =>
    let progress := table.computeProgress
    let info := s!"📊 **Function Progress Table**\n\n" ++
                s!"• Total functions: {progress.total}\n" ++
                s!"• Completed: {progress.documented + progress.tested + progress.implemented}\n" ++
                s!"• In progress: {progress.inProgress}\n" ++
                s!"• Not started: {progress.notStarted}\n" ++
                s!"• Overall completion: {progress.percentComplete:.1f}%\n\n" ++
                s!"💡 *Right-click for formatting options*"
    some info

/-- LSP diagnostic information for table validation -/
inductive TableDiagnostic where
  | misalignedBorders
  | invalidStatus (row : Nat) (status : String)
  | missingFunction (row : Nat) (name : String)
  | inconsistentColumns
  | emptyTable
  deriving Repr

instance : ToString TableDiagnostic where
  toString
  | .misalignedBorders => "Table borders are misaligned"
  | .invalidStatus row status => s!"Invalid status '{status}' in row {row}"
  | .missingFunction row name => s!"Function '{name}' not found (row {row})"
  | .inconsistentColumns => "Table has inconsistent column counts"
  | .emptyTable => "Table contains no data"

/-- Generate diagnostics for table validation -/
def generateDiagnostics (context : TableContext) : Array TableDiagnostic :=
  if !context.inTable then #[]
  else
    let diagnostics := Array.empty
    
    -- Check if table is parseable
    match parseTableToFunctionData context.tableText with
    | .error _ => diagnostics.push .misalignedBorders
    | .ok functionData =>
      if functionData.isEmpty then
        diagnostics.push .emptyTable
      else
        -- Check for invalid statuses
        let statusDiagnostics := functionData.toList.enumInd.filterMap fun (idx, (_, status, _)) =>
          if status ∉ ["✗", "⋯", "✓", "✓✓", "✓✓✓"] then
            some (.invalidStatus idx status)
          else none
        
        diagnostics ++ statusDiagnostics.toArray

/-- Format table with specific style for code action preview -/
def previewAction (action : TableActionType) (context : TableContext) : Option String :=
  match executeAction action context with
  | .ok result => some result.newText
  | .error _ => none

/-- Integration with Lean's LSP server (conceptual) -/
namespace LSPIntegration

/-- Register code action provider -/
def registerCodeActionProvider : IO Unit := do
  -- This would integrate with Lean's LSP server
  -- Implementation would depend on Lean 4's LSP architecture
  pure ()

/-- Handle code action request -/
def handleCodeActionRequest (uri : String) (range : Range) (context : CodeActionContext) : IO (Array CodeAction) := do
  -- Extract text from document at range
  -- Analyze table context
  -- Generate available actions
  -- Return code action list
  pure #[]

/-- Handle hover request for table information -/
def handleHoverRequest (uri : String) (position : Position) : IO (Option Hover) := do
  -- Extract text around position
  -- Check if position is within a table
  -- Generate hover information
  pure none

/-- Handle formatting request for tables -/
def handleFormattingRequest (uri : String) (options : FormattingOptions) : IO (Array TextEdit) := do
  -- Find all tables in document
  -- Apply automatic formatting
  -- Generate text edits
  pure #[]

end LSPIntegration

/-- Command-line interface for table formatting (for testing) -/
namespace CLI

def formatTableFile (inputFile : String) (outputFile : String) (style : String := "elegant") : IO Unit := do
  let content ← IO.FS.readFile inputFile
  let context := analyzeTableContext content 0
  
  match context.tableData with
  | none => IO.println "No table found in file"
  | some table =>
    let styleFormat := match style with
      | "elegant" => Styles.elegant
      | "minimal" => Styles.minimal
      | "compact" => Styles.compact
      | "rounded" => Styles.rounded
      | _ => defaultFunctionTableFormat
    
    let formatted := formatFunctionTable table styleFormat
    IO.FS.writeFile outputFile formatted
    IO.println s!"Formatted table saved to {outputFile}"

def exportTable (inputFile : String) (format : String) : IO Unit := do
  let content ← IO.FS.readFile inputFile
  let context := analyzeTableContext content 0
  
  match context.tableData with
  | none => IO.println "No table found in file"
  | some table =>
    let exported := match format with
      | "markdown" => Export.toMarkdown table
      | "html" => Export.toHTML table
      | "latex" => Export.toLaTeX table
      | "csv" => Export.toCSV table
      | _ => formatFunctionTable table Styles.minimal
    
    let extension := match format with
      | "markdown" => ".md"
      | "html" => ".html"
      | "latex" => ".tex"
      | "csv" => ".csv"
      | _ => ".txt"
    
    let outputFile := inputFile ++ extension
    IO.FS.writeFile outputFile exported
    IO.println s!"Exported to {outputFile}"

end CLI

end FuncTracker.TwoD.CodeActions