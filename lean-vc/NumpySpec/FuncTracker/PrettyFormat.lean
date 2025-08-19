import FuncTracker.BasicV2
import FuncTracker.TwoDSyntax
import FuncTracker.BoxDrawing

namespace FuncTracker.TwoD.PrettyFormat

open FuncTracker
open FuncTracker.TwoD
open FuncTracker.TwoD.BoxDrawing

/-!
# PrettyFormat - Advanced Table Formatting and Beautification

This module provides sophisticated table formatting capabilities for Phase 2,
including dynamic column sizing, styling options, and multiple export formats.

## Key Features

- **Dynamic Column Sizing**: Automatically calculate optimal column widths
- **Style Customization**: Support different border styles and alignments
- **Multi-format Export**: Generate Markdown, HTML, LaTeX, and ASCII
- **Content Analysis**: Intelligent padding and alignment based on content type
- **Unicode Perfection**: Professional-grade box-drawing character usage

## Design Philosophy

Build a formatting engine that's both beautiful and functional:
- Analyze content to determine optimal layout
- Support multiple output formats from single source
- Provide rich styling options while maintaining readability
- Enable both automatic and manual formatting control
-/

/-- Text alignment options for table cells -/
inductive TextAlignment where
  | left
  | center  
  | right
  deriving Repr, BEq, DecidableEq

instance : ToString TextAlignment where
  toString
  | .left => "left"
  | .center => "center"
  | .right => "right"

/-- Border style variations for different aesthetics -/
inductive BorderStyle where
  /-- Heavy double-line borders (default) -/
  | heavy
  /-- Light single-line borders -/
  | light
  /-- Rounded corners -/
  | rounded
  /-- No borders (CSV-like) -/
  | none
  deriving Repr, BEq, DecidableEq

/-- Column formatting specification -/
structure ColumnFormat where
  /-- Minimum width for this column -/
  minWidth : Nat
  /-- Maximum width for this column (0 = unlimited) -/
  maxWidth : Nat := 0
  /-- Text alignment within the column -/
  alignment : TextAlignment := .left
  /-- Custom padding (left, right) -/
  padding : Nat × Nat := (1, 1)
  deriving Repr, BEq

/-- Complete table formatting specification -/
structure TableFormat where
  /-- Border style to use -/
  borderStyle : BorderStyle := .heavy
  /-- Column-specific formatting -/
  columnFormats : Array ColumnFormat := #[]
  /-- Whether to include header separator -/
  includeHeaderSeparator : Bool := true
  /-- Custom cell separator for CSV-like output -/
  cellSeparator : String := "│"
  /-- Line separator for different row types -/
  lineSeparator : String := "\n"
  deriving Repr

/-- Default formatting for function tracking tables -/
def defaultFunctionTableFormat : TableFormat := {
  borderStyle := .heavy,
  columnFormats := #[
    { minWidth := 15, alignment := .left },   -- Function name
    { minWidth := 10, alignment := .center }, -- Status  
    { minWidth := 12, alignment := .left }    -- File
  ],
  includeHeaderSeparator := true
}

/-- Analyze content to determine optimal column widths -/
def analyzeColumnWidths (content : Array (Array String)) (format : TableFormat) : Array Nat :=
  if content.isEmpty then #[]
  else
    let numCols := content[0]!.size
    Array.range numCols |>.map fun colIdx =>
      -- Find the maximum width needed for this column
      let contentWidth := content.foldl (fun maxW row =>
        if h : colIdx < row.size then
          max maxW row[colIdx]'h.length
        else maxW
      ) 0
      
      -- Apply column format constraints
      let colFormat := if h : colIdx < format.columnFormats.size then
        format.columnFormats[colIdx]'h
      else
        { minWidth := 8, alignment := .left, padding := (1, 1) }
      
      let paddingWidth := colFormat.padding.1 + colFormat.padding.2
      let baseWidth := max contentWidth colFormat.minWidth
      let finalWidth := if colFormat.maxWidth > 0 then
        min baseWidth colFormat.maxWidth
      else baseWidth
      
      finalWidth + paddingWidth

/-- Apply text alignment within a cell -/
def alignText (text : String) (width : Nat) (alignment : TextAlignment) : String :=
  let trimmed := text.take width
  let padNeeded := width - trimmed.length
  
  match alignment with
  | .left => trimmed ++ String.mk (List.replicate padNeeded ' ')
  | .right => String.mk (List.replicate padNeeded ' ') ++ trimmed
  | .center =>
    let leftPad := padNeeded / 2
    let rightPad := padNeeded - leftPad
    String.mk (List.replicate leftPad ' ') ++ trimmed ++ String.mk (List.replicate rightPad ' ')

/-- Generate border characters for different styles -/
def getBorderChars (style : BorderStyle) : 
  (topLeft : Char) × (topRight : Char) × (bottomLeft : Char) × (bottomRight : Char) ×
  (horizontal : Char) × (vertical : Char) × (cross : Char) ×
  (teeDown : Char) × (teeUp : Char) × (teeLeft : Char) × (teeRight : Char) :=
  match style with
  | .heavy => ('╔', '╗', '╚', '╝', '═', '║', '╬', '╦', '╩', '╣', '╠')
  | .light => ('┌', '┐', '└', '┘', '─', '│', '┼', '┬', '┴', '┤', '├')
  | .rounded => ('╭', '╮', '╰', '╯', '─', '│', '┼', '┬', '┴', '┤', '├')
  | .none => (' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ')

/-- Generate a formatted table border line -/
def generateBorderLine (columnWidths : Array Nat) (style : BorderStyle) (lineType : String) : String :=
  if columnWidths.isEmpty then ""
  else
    let chars := getBorderChars style
    let (leftChar, rightChar, fillChar, junctionChar) := match lineType with
      | "top" => (chars.1, chars.2.1, chars.2.2.2.2.1, chars.2.2.2.2.2.2.2.1)
      | "bottom" => (chars.2.1, chars.2.2.1, chars.2.2.2.2.1, chars.2.2.2.2.2.2.2.2.1)
      | "separator" => (chars.2.2.2.2.2.2.2.2.2.1, chars.2.2.2.2.2.2.2.2.2.2.1, chars.2.2.2.2.1, chars.2.2.2.1)
      | _ => (chars.1, chars.2.1, chars.2.2.2.2.1, chars.2.2.2.1)
    
    let segments := columnWidths.toList.map fun width =>
      String.mk (List.replicate width fillChar)
    
    leftChar.toString ++ String.intercalate junctionChar.toString segments ++ rightChar.toString

/-- Format a single data row -/
def formatDataRow (row : Array String) (columnWidths : Array Nat) (format : TableFormat) : String :=
  if row.isEmpty || columnWidths.isEmpty then ""
  else
    let chars := getBorderChars format.borderStyle
    let verticalChar := chars.2.2.2.2.2.1
    
    let formattedCells := row.toList.zip columnWidths.toList |>.enumInd.map fun (colIdx, (cellContent, width)) =>
      let colFormat := if h : colIdx < format.columnFormats.size then
        format.columnFormats[colIdx]'h
      else
        { minWidth := width, alignment := .left, padding := (1, 1) }
      
      let paddedWidth := width - colFormat.padding.1 - colFormat.padding.2
      let aligned := alignText cellContent paddedWidth colFormat.alignment
      String.mk (List.replicate colFormat.padding.1 ' ') ++ aligned ++ 
      String.mk (List.replicate colFormat.padding.2 ' ')
    
    if format.borderStyle == .none then
      String.intercalate format.cellSeparator formattedCells
    else
      verticalChar.toString ++ String.intercalate verticalChar.toString formattedCells ++ verticalChar.toString

/-- Generate a beautifully formatted table -/
def formatTable (headers : Array String) (rows : Array (Array String)) (format : TableFormat) : String :=
  if headers.isEmpty && rows.isEmpty then ""
  else
    -- Combine headers and data for width analysis
    let allContent := if headers.isEmpty then rows else #[headers] ++ rows
    let columnWidths := analyzeColumnWidths allContent format
    
    let result := 
      -- Top border
      if format.borderStyle != .none then
        [generateBorderLine columnWidths format.borderStyle "top"]
      else []
    
    let result := result ++
      -- Header row
      if !headers.isEmpty then
        [formatDataRow headers columnWidths format]
      else []
    
    let result := result ++
      -- Header separator
      if !headers.isEmpty && format.includeHeaderSeparator && format.borderStyle != .none then
        [generateBorderLine columnWidths format.borderStyle "separator"]
      else []
    
    let result := result ++
      -- Data rows
      rows.toList.map (formatDataRow · columnWidths format)
    
    let result := result ++
      -- Bottom border
      if format.borderStyle != .none then
        [generateBorderLine columnWidths format.borderStyle "bottom"]
      else []
    
    String.intercalate format.lineSeparator result

/-- Convert FunctionTable to beautiful formatted table -/
def formatFunctionTable (table : FunctionTable) (format : TableFormat := defaultFunctionTableFormat) : String :=
  let headers := #["Function", "Status", "File"]
  let rows := table.functions.map fun f => 
    #[f.name.toString, f.status.toSymbol, f.file.getD "-"]
  formatTable headers rows format

/-- Export formats for different target environments -/
namespace Export

/-- Generate Markdown table -/
def toMarkdown (table : FunctionTable) : String :=
  let markdownFormat : TableFormat := {
    borderStyle := .none,
    cellSeparator := " | ",
    columnFormats := #[
      { minWidth := 0, alignment := .left },
      { minWidth := 0, alignment := .center },
      { minWidth := 0, alignment := .left }
    ],
    includeHeaderSeparator := false
  }
  
  let headers := #["Function", "Status", "File"]
  let rows := table.functions.map fun f => 
    #[f.name.toString, f.status.toSymbol, f.file.getD "-"]
  
  let headerLine := "| " ++ String.intercalate " | " headers.toList ++ " |"
  let separatorLine := "| " ++ String.intercalate " | " (headers.map (fun _ => "---")).toList ++ " |"
  let dataLines := rows.toList.map fun row =>
    "| " ++ String.intercalate " | " row.toList ++ " |"
  
  String.intercalate "\n" ([headerLine, separatorLine] ++ dataLines)

/-- Generate HTML table -/
def toHTML (table : FunctionTable) (cssClass : String := "func-table") : String :=
  let headers := ["Function", "Status", "File"]
  let headerRow := "  <tr>" ++ String.intercalate "" (headers.map (fun h => s!"<th>{h}</th>")) ++ "</tr>"
  
  let dataRows := table.functions.toList.map fun f =>
    let cells := [f.name.toString, f.status.toSymbol, f.file.getD "-"]
    "  <tr>" ++ String.intercalate "" (cells.map (fun c => s!"<td>{c}</td>")) ++ "</tr>"
  
  s!"<table class=\"{cssClass}\">\n{headerRow}\n" ++ 
  String.intercalate "\n" dataRows ++ "\n</table>"

/-- Generate LaTeX table -/
def toLaTeX (table : FunctionTable) : String :=
  let columnSpec := "lcc"  -- left, center, center
  let headers := ["Function", "Status", "File"]
  let headerRow := String.intercalate " & " headers ++ " \\\\"
  
  let dataRows := table.functions.toList.map fun f =>
    let cells := [f.name.toString, f.status.toSymbol, f.file.getD "-"]
    String.intercalate " & " cells ++ " \\\\"
  
  s!"\\begin{{tabular}}{{{columnSpec}}}\n\\hline\n{headerRow}\n\\hline\n" ++
  String.intercalate "\n" dataRows ++ "\n\\hline\n\\end{tabular}"

/-- Generate CSV format -/
def toCSV (table : FunctionTable) (separator : String := ",") : String :=
  let headers := ["Function", "Status", "File"]
  let headerLine := String.intercalate separator headers
  
  let dataLines := table.functions.toList.map fun f =>
    let cells := [f.name.toString, f.status.toSymbol, f.file.getD "-"]
    String.intercalate separator cells
  
  String.intercalate "\n" ([headerLine] ++ dataLines)

end Export

/-- Style presets for common use cases -/
namespace Styles

def minimal : TableFormat := {
  borderStyle := .light,
  columnFormats := #[
    { minWidth := 10, alignment := .left, padding := (1, 1) },
    { minWidth := 6, alignment := .center, padding := (1, 1) },
    { minWidth := 8, alignment := .left, padding := (1, 1) }
  ]
}

def elegant : TableFormat := {
  borderStyle := .heavy,
  columnFormats := #[
    { minWidth := 20, alignment := .left, padding := (2, 2) },
    { minWidth := 12, alignment := .center, padding := (2, 2) },
    { minWidth := 15, alignment := .left, padding := (2, 2) }
  ]
}

def compact : TableFormat := {
  borderStyle := .light,
  columnFormats := #[
    { minWidth := 8, alignment := .left, padding := (0, 1) },
    { minWidth := 4, alignment := .center, padding := (0, 1) },
    { minWidth := 6, alignment := .left, padding := (0, 1) }
  ]
}

def rounded : TableFormat := {
  borderStyle := .rounded,
  columnFormats := #[
    { minWidth := 15, alignment := .left, padding := (1, 1) },
    { minWidth := 10, alignment := .center, padding := (1, 1) },
    { minWidth := 12, alignment := .left, padding := (1, 1) }
  ]
}

end Styles

end FuncTracker.TwoD.PrettyFormat