import Lean
import Std.Internal.Parsec
import FuncTracker.BasicV2

namespace FuncTracker

open Std.Internal.Parsec
open Std.Internal.Parsec.String

/-- Enhanced cell type supporting spanning and content types -/
inductive EnhancedGridCell where
  | content : String → EnhancedGridCell
  | spanned : String → Nat → EnhancedGridCell  -- content, span width
  | continuation : EnhancedGridCell              -- marker for spanned cells
  | border : Char → EnhancedGridCell
  | empty : EnhancedGridCell
  deriving Repr, BEq

instance : Inhabited EnhancedGridCell where
  default := .empty

/-- Cell position in the grid -/
structure CellPosition where
  row : Nat
  col : Nat
  deriving Repr, BEq, DecidableEq

/-- Enhanced grid with cell spanning support -/
structure EnhancedGrid where
  cells : Array (Array EnhancedGridCell)
  rows : Nat
  cols : Nat
  /-- Track which cells are spanned by others -/
  spanMap : Array (CellPosition × Nat)  -- (origin, span_width)
  deriving Repr

/-- Convert enhanced cell to display string -/
def EnhancedGridCell.toString : EnhancedGridCell → String
  | .content s => s
  | .spanned s _ => s
  | .continuation => "cont"
  | .border c => c.toString
  | .empty => ""

instance : ToString EnhancedGridCell where
  toString := EnhancedGridCell.toString

namespace EnhancedGridParser

/-- Parse whitespace -/
def ws : Parser Unit := do
  let _ ← many (satisfy (fun c => c == ' ' || c == '\t'))
  pure ()

/-- Parse many characters satisfying a predicate -/
def manyChars (p : Char → Bool) : Parser String := do
  let chars ← many (satisfy p)
  return String.mk chars.toList

/-- Parse a specific character -/
def pchar (c : Char) : Parser Char := 
  satisfy (· == c)

/-- Manual implementation of sepBy1 for parsers -/
def sepBy1 (p : Parser α) (sep : Parser β) : Parser (Array α) := do
  let first ← p
  let rest ← many (sep *> p)
  return #[first] ++ rest

/-- Parse horizontal border with variable length: ═══ -/
def hBorder : Parser (Array Char) := do
  many1 (pchar '═')

/-- Parse top border with column detection: ╔═══╦═══╗ -/
def topBorderWithColumns : Parser (Array Nat) := do
  let _ ← pchar '╔'
  let segments ← sepBy1 hBorder (pchar '╦')
  let _ ← pchar '╗'
  let _ ← optional (pchar '\n')
  return segments.map (·.size)

/-- Parse bottom border: ╚═══╝ -/
def bottomBorder : Parser Unit := do
  let _ ← pchar '╚'
  let _ ← hBorder
  let _ ← pchar '╝'
  pure ()

/-- Parse separator border with column alignment: ╠═══╬═══╣ -/
def separatorBorderWithColumns : Parser Unit := do
  let _ ← pchar '╠'
  let _ ← hBorder
  let _ ← many (pchar '╬' *> hBorder)
  let _ ← pchar '╣'
  let _ ← optional (pchar '\n')
  pure ()

/-- Parse enhanced cell content with spanning markers -/
def enhancedCellContent : Parser String := do
  let chars ← manyChars (fun c => c != '│' && c != '\n')
  pure chars.trim

/-- Detect if a cell content indicates spanning (contains continuation marker) -/
def isSpanningContent (content : String) : Bool :=
  content.isEmpty || content.trim == "cont" || content.trim == "→"

/-- Parse a row with enhanced cell detection -/
def parseEnhancedRow (columnWidths : Array Nat) : Parser (Array EnhancedGridCell) := do
  let _ ← pchar '│'
  let cellContents ← sepBy1 enhancedCellContent (pchar '│')
  let _ ← optional (pchar '\n')
  
  -- Convert cell contents to enhanced cells
  let enhancedCells := cellContents.mapIdx fun i content =>
    if isSpanningContent content then
      .continuation
    else
      -- Check if this cell should span (simple heuristic: long content)
      if content.length > 20 then
        .spanned content 2
      else
        .content content
  
  return enhancedCells

/-- Parse header row to determine column structure -/
def parseHeaderRow : Parser (Array String) := do
  let _ ← pchar '│'
  let headers ← sepBy1 enhancedCellContent (pchar '│')
  let _ ← optional (pchar '\n')
  return headers

/-- Parse the complete enhanced grid -/
def parseEnhancedGrid : Parser EnhancedGrid := do
  -- Parse top border to detect column structure
  let columnWidths ← topBorderWithColumns
  
  -- Parse header row
  let headerCells ← parseHeaderRow
  
  -- Parse separator
  let _ ← separatorBorderWithColumns
  
  -- Parse data rows
  let dataRows ← many (parseEnhancedRow columnWidths)
  
  -- Parse bottom border
  let _ ← bottomBorder
  
  -- Construct the enhanced grid
  let allCells := #[headerCells.map EnhancedGridCell.content] ++ dataRows
  let rows := allCells.size
  let cols := if headerCells.size > 0 then headerCells.size else 0
  
  return {
    cells := allCells,
    rows := rows,
    cols := cols,
    spanMap := #[]  -- TODO: Properly calculate span map
  }

end EnhancedGridParser

-- Enhanced grid operations inspired by Racket 2D
namespace EnhancedGrid

/-- Get cell at position, handling spanning -/
def getCell (grid : EnhancedGrid) (pos : CellPosition) : Option EnhancedGridCell :=
  if pos.row < grid.rows && pos.col < grid.cols then
    some grid.cells[pos.row]![pos.col]!
  else
    none

/-- Check if a position is within a spanned region -/
def isInSpannedRegion (grid : EnhancedGrid) (pos : CellPosition) : Bool :=
  grid.spanMap.any fun (entry : CellPosition × Nat) =>
    let origin : CellPosition := entry.1
    let span : Nat := entry.2
    origin.row == pos.row && origin.col <= pos.col && pos.col < origin.col + span

/-- Get the origin cell for a spanned position -/
def getSpanOrigin (grid : EnhancedGrid) (pos : CellPosition) : Option CellPosition :=
  match grid.spanMap.find? fun (entry : CellPosition × Nat) =>
    let origin : CellPosition := entry.1
    let span : Nat := entry.2
    origin.row == pos.row && origin.col <= pos.col && pos.col < origin.col + span with
  | some entry => some entry.1
  | none => none

/-- Create a spanned cell at the given position -/
def createSpannedCell (grid : EnhancedGrid) (pos : CellPosition) (content : String) (span : Nat) : EnhancedGrid :=
  let newSpanEntry := (pos, span)
  let updatedCells := grid.cells.mapIdx fun rowIdx row =>
    if rowIdx == pos.row then
      row.mapIdx fun colIdx cell =>
        if colIdx == pos.col then
          .spanned content span
        else if colIdx > pos.col && colIdx < pos.col + span then
          .continuation
        else
          cell
    else
      row
  
  { grid with
    cells := updatedCells,
    spanMap := grid.spanMap.push newSpanEntry }

/-- Convert enhanced grid to ASCII representation -/
def toAscii (grid : EnhancedGrid) : String :=
  let header := "╔" ++ String.mk (List.replicate (grid.cols * 8) '═') ++ "╗\n"
  let footer := "╚" ++ String.mk (List.replicate (grid.cols * 8) '═') ++ "╝"
  
  let rows := grid.cells.toList.map fun row =>
    "│" ++ String.intercalate "│" (row.toList.map fun cell => 
      let s := cell.toString.take 7
      s ++ String.mk (List.replicate (7 - s.length) ' ')) ++ "│"
  
  header ++ String.intercalate "\n" rows ++ "\n" ++ footer

/-- 2D constraint checking inspired by Racket 2D -/
def checkConstraint (grid : EnhancedGrid) (constraint : CellPosition → CellPosition → Bool) : Bool :=
  (List.range grid.rows).all fun row =>
    (List.range grid.cols).all fun col =>
      let pos1 := ⟨row, col⟩
      (List.range grid.cols).all fun col2 =>
        let pos2 := ⟨row, col2⟩
        constraint pos1 pos2

/-- Spatial relationship predicates -/
def isAdjacent (pos1 pos2 : CellPosition) : Bool :=
  (pos1.row == pos2.row && (pos1.col + 1 == pos2.col || pos2.col + 1 == pos1.col)) ||
  (pos1.col == pos2.col && (pos1.row + 1 == pos2.row || pos2.row + 1 == pos1.row))

def isInSameRow (pos1 pos2 : CellPosition) : Bool :=
  pos1.row == pos2.row

def isInSameColumn (pos1 pos2 : CellPosition) : Bool :=
  pos1.col == pos2.col

/-- Enhanced validation with spatial predicates -/
def validateSpatialConstraint (grid : EnhancedGrid) (pred : CellPosition → CellPosition → Bool) : Array (CellPosition × CellPosition) :=
  let violations := (List.range grid.rows).foldl (init := #[]) fun acc row =>
    (List.range grid.cols).foldl (init := acc) fun acc2 col =>
      let pos1 := ⟨row, col⟩
      (List.range grid.cols).foldl (init := acc2) fun acc3 col2 =>
        let pos2 := ⟨row, col2⟩
        if ¬pred pos1 pos2 then
          acc3.push (pos1, pos2)
        else
          acc3
  violations

end EnhancedGrid

/-- Parse status from string (enhanced to handle spanned cells) -/
def parseStatus (s : String) : Status :=
  match s.trim with
  | "✗" => Status.notStarted
  | "⋯" => Status.inProgress
  | "✓" => Status.implemented
  | "✓✓" => Status.tested
  | "✓✓✓" => Status.documented
  | "cont" => Status.notStarted  -- Continuation cells default to not started
  | _ => Status.notStarted

/-- Integration with existing FuncTracker system -/
def enhancedGridToFunctionTable (grid : EnhancedGrid) : FunctionTable :=
  if grid.rows <= 1 then
    { functions := #[] }
  else
    let functions := (List.range (grid.rows - 1)).map fun i =>
      let row := grid.cells[i + 1]!  -- Skip header row
      let name := if row.size > 0 then row[0]!.toString else ""
      let status := if row.size > 1 then 
        parseStatus row[1]!.toString
      else
        Status.notStarted
      {
        name := stringToName name,
        status := status,
        file := if row.size > 2 then some row[2]!.toString else none,
        lines := none,
        complexity := none,
        docString := none,
        versoLink := none,
        refs := #[],
        typedRefs := #[],
        version := none
      }
    { functions := functions.toArray }

end FuncTracker