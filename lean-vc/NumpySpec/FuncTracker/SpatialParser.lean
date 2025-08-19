import Lean
import Std.Internal.Parsec
import FuncTracker.TwoDSyntax
import FuncTracker.BoxDrawing

namespace FuncTracker.TwoD.SpatialParser

open Lean
open Std.Internal.Parsec.String
open FuncTracker.TwoD
open FuncTracker.TwoD.BoxDrawing

/-!
# SpatialParser - 2D Layout Parsing Engine

This module implements the core parsing logic for 2D table layouts, inspired by 
Racket's 2D reader. It understands spatial relationships between cells and 
converts visual table layouts into structured data.

## Parsing Strategy

1. **Line-by-line tokenization**: Break input into lines, then parse each line
2. **Character classification**: Identify box-drawing characters vs. content
3. **Grid structure detection**: Find table boundaries and cell separators
4. **Cell extraction**: Extract content from within the grid structure
5. **Spatial relationship preservation**: Maintain row/column information

## Design Principles

- **Forgiving parsing**: Handle slightly misaligned tables gracefully
- **Error recovery**: Provide helpful error messages for malformed tables
- **Incremental construction**: Build the grid step by step
- **Type safety**: Ensure parsed structure is well-formed
-/

/-- Raw parsed line containing a mix of box-drawing and content characters -/
structure ParsedLine where
  /-- Line number (0-indexed) -/
  lineNum : Nat
  /-- Characters in this line -/
  chars : Array Char
  /-- Positions of box-drawing characters -/
  boxPositions : Array Nat
  deriving Repr

/-- Parse result for a single line -/
inductive LineParseResult where
  /-- Successfully parsed table row -/
  | tableRow : ParsedLine → LineParseResult
  /-- Border line (top, bottom, or separator) -/
  | border : ParsedLine → LineParseResult
  /-- Empty or whitespace-only line -/
  | empty : LineParseResult
  /-- Parse error -/
  | error : String → LineParseResult
  deriving Repr

/-- Parse a single line and classify its type -/
def parseLine (lineNum : Nat) (line : String) : LineParseResult :=
  if line.trim.isEmpty then
    .empty
  else
    let chars := line.toList.toArray
    let boxPositions := chars.toList.enumInd.filter (fun (_, c) => isBoxDrawingChar c) |>.map (·.1) |>.toArray
    let parsed := { lineNum := lineNum, chars := chars, boxPositions := boxPositions }
    
    -- Classify line type based on box-drawing character pattern
    if boxPositions.size > 0 then
      let hasVertical := chars.any isVertical
      let hasHorizontal := chars.any isHorizontal
      let hasCorner := chars.any isCorner
      let hasJunction := chars.any isJunction
      
      if hasCorner || (hasHorizontal && hasJunction) then
        .border parsed
      else if hasVertical then
        .tableRow parsed
      else
        .border parsed
    else
      .error s!"Line {lineNum}: No table structure found"

/-- Extract cell content from between vertical separators -/
def extractCellsFromLine (parsed : ParsedLine) : Array String :=
  let chars := parsed.chars
  let verticalPositions := chars.toList.enumInd.filter (fun (_, c) => isVertical c) |>.map (·.1)
  
  -- Extract content between consecutive vertical bars
  let rec extractBetween (positions : List Nat) (acc : Array String) : Array String :=
    match positions with
    | [] => acc
    | [_] => acc
    | pos1 :: pos2 :: rest =>
      let startIdx := pos1 + 1
      let endIdx := pos2
      if startIdx < endIdx && endIdx <= chars.size then
        let cellChars := chars.toList.drop startIdx |>.take (endIdx - startIdx)
        let cellContent := String.mk cellChars |>.trim
        extractBetween (pos2 :: rest) (acc.push cellContent)
      else
        extractBetween (pos2 :: rest) acc
  
  extractBetween verticalPositions #[]

/-- Parse column structure from a border line -/
def parseColumnStructure (parsed : ParsedLine) : Array Nat :=
  let chars := parsed.chars.toList
  let junctionPositions := chars.enumInd.filter (fun (_, c) => isJunction c || isCorner c) |>.map (·.1)
  
  -- Calculate column widths from junction positions
  let rec calculateWidths (positions : List Nat) (acc : Array Nat) : Array Nat :=
    match positions with
    | [] => acc
    | [_] => acc
    | pos1 :: pos2 :: rest =>
      let width := pos2 - pos1 - 1  -- -1 to exclude the junction character itself
      calculateWidths (pos2 :: rest) (acc.push width.toNat)
  
  calculateWidths junctionPositions #[]

/-- Complete 2D table parsing result -/
structure ParsedTable where
  /-- Column widths detected from the table structure -/
  columnWidths : Array Nat
  /-- Parsed table rows with cell content -/
  rows : Array (Array String)
  /-- Original line count -/
  lineCount : Nat
  deriving Repr

/-- Parse a complete 2D table from multi-line input -/
def parseTable (input : String) : Except String ParsedTable :=
  let lines := input.splitOn "\n"
  let parsedLines := lines.enumInd.map (fun (i, line) => parseLine i line)
  
  -- Separate borders from content rows
  let borders := parsedLines.filterMap fun result =>
    match result with
    | .border parsed => some parsed
    | _ => none
  
  let contentRows := parsedLines.filterMap fun result =>
    match result with
    | .tableRow parsed => some parsed
    | _ => none
  
  -- Extract column structure from first border
  if borders.isEmpty then
    .error "No table borders found"
  else
    let firstBorder := borders[0]!
    let columnWidths := parseColumnStructure firstBorder
    
    if columnWidths.isEmpty then
      .error "Could not detect table column structure"
    else
      -- Extract cell content from each row
      let rows := contentRows.map extractCellsFromLine
      
      -- Validate that all rows have the expected number of columns
      let expectedCols := columnWidths.size
      let invalidRows := rows.filter (fun row => row.size != expectedCols)
      
      if invalidRows.isEmpty then
        .ok {
          columnWidths := columnWidths,
          rows := rows,
          lineCount := lines.length
        }
      else
        .error s!"Inconsistent column count: expected {expectedCols}, found rows with different counts"

/-- Convert parsed table to TwoDGrid -/
def parsedTableToGrid (table : ParsedTable) : TwoDGrid :=
  let gridRows := table.rows.toList.enumInd.map fun (rowIdx, cells) =>
    let gridCells := cells.map fun cellContent =>
      if cellContent.isEmpty then .empty else .content cellContent
    { cells := gridCells, rowNum := rowIdx }
  
  {
    rows := gridRows.toArray,
    cols := table.columnWidths.size
  }

/-- Simple parser for minimally aligned tables (Phase 1 approach) -/
def parseSimpleTable (input : String) : Except String TwoDGrid :=
  match parseTable input with
  | .ok parsed => .ok (parsedTableToGrid parsed)
  | .error msg => .error msg

/-- Enhanced parser with spatial validation (for future phases) -/
def parseSpatialTable (input : String) : Except String TwoDGrid :=
  -- Start with simple parsing
  match parseSimpleTable input with
  | .ok grid =>
    -- Add spatial validation
    if grid.isWellFormed then
      .ok grid
    else
      .error "Grid structure is not well-formed"
  | .error msg => .error msg

/-- Parse table and extract function tracking data -/
def parseTableToFunctionData (input : String) : Except String (Array (String × String × Option String)) :=
  match parseTable input with
  | .ok parsed =>
    if parsed.columnWidths.size < 2 then
      .error "Table must have at least 2 columns (Name, Status)"
    else
      let functionData := parsed.rows.map fun row =>
        let name := if row.size > 0 then row[0]! else ""
        let status := if row.size > 1 then row[1]! else ""
        let file := if row.size > 2 then some row[2]! else none
        (name, status, file)
      .ok functionData
  | .error msg => .error msg

/-- Pretty-print parsing diagnostics -/
def formatParsingDiagnostics (input : String) : String :=
  let lines := input.splitOn "\n"
  let results := lines.enumInd.map (fun (i, line) => (i, parseLine i line))
  
  let diagnostics := results.map fun (lineNum, result) =>
    match result with
    | .tableRow _ => s!"Line {lineNum}: Table row ✓"
    | .border _ => s!"Line {lineNum}: Border ✓"
    | .empty => s!"Line {lineNum}: Empty"
    | .error msg => s!"Line {lineNum}: Error - {msg}"
  
  String.intercalate "\n" diagnostics.toList

/-- Test if input looks like a 2D table -/
def looksLikeTable (input : String) : Bool :=
  let lines := input.splitOn "\n"
  let hasBoxChars := lines.any fun line => line.any isBoxDrawingChar
  let hasMultipleLines := lines.length > 2
  hasBoxChars && hasMultipleLines

end FuncTracker.TwoD.SpatialParser