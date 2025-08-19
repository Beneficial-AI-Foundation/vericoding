import Lean
import Std.Internal.Parsec

namespace FuncTracker.TwoD

open Lean

/-!
# TwoDSyntax - Core 2D Parsing Infrastructure

This module provides the foundation for native 2D syntax parsing in Lean 4,
inspired by Racket's #2d reader. Instead of parsing strings, we treat 2D 
layouts as first-class syntax elements.

## Key Concepts

- **2D Position**: Row and column coordinates in the visual layout
- **Cell**: A rectangular region containing expressions
- **Grid**: A 2D arrangement of cells with spatial relationships
- **Box Drawing**: Unicode characters that define table structure

## Design Philosophy

Follow the same compositional approach as our parser combinators:
- Start with atomic 2D elements (positions, cells)
- Build larger structures (rows, grids) functorially
- Preserve spatial relationships throughout parsing
- Enable beautiful pretty-printing from the parsed structure
-/

/-- A position in 2D space representing row and column coordinates -/
structure TwoDPosition where
  /-- Row coordinate (0-indexed from top) -/
  row : Nat
  /-- Column coordinate (0-indexed from left) -/
  col : Nat
  deriving Repr, BEq, DecidableEq, Ord

instance : ToString TwoDPosition where
  toString pos := s!"({pos.row}, {pos.col})"

/-- A rectangular region in 2D space -/
structure TwoDRegion where
  /-- Top-left position -/
  topLeft : TwoDPosition
  /-- Bottom-right position (inclusive) -/
  bottomRight : TwoDPosition
  /-- Ensure region is well-formed -/
  valid : topLeft.row ≤ bottomRight.row ∧ topLeft.col ≤ bottomRight.col
  deriving Repr

/-- Check if a position is within a region -/
def TwoDPosition.inRegion (pos : TwoDPosition) (region : TwoDRegion) : Bool :=
  region.topLeft.row ≤ pos.row ∧ pos.row ≤ region.bottomRight.row ∧
  region.topLeft.col ≤ pos.col ∧ pos.col ≤ region.bottomRight.col

/-- Get all positions within a region -/
def TwoDRegion.positions (region : TwoDRegion) : List TwoDPosition :=
  let rows := List.range (region.bottomRight.row - region.topLeft.row + 1) |>.map (· + region.topLeft.row)
  let cols := List.range (region.bottomRight.col - region.topLeft.col + 1) |>.map (· + region.topLeft.col)
  rows.flatMap fun r => cols.map fun c => ⟨r, c⟩

/-- Box-drawing character classification -/
inductive BoxChar where
  /-- Corner characters: ╔ ╗ ╚ ╝ -/
  | corner : (topLeft : Bool) → (topRight : Bool) → (bottomLeft : Bool) → (bottomRight : Bool) → BoxChar
  /-- Horizontal line: ═ -/
  | horizontal : BoxChar
  /-- Vertical line: ║ -/
  | vertical : BoxChar
  /-- Junction characters: ╦ ╩ ╠ ╣ ╬ -/
  | junction : (up : Bool) → (down : Bool) → (left : Bool) → (right : Bool) → BoxChar
  deriving Repr, BEq, DecidableEq

/-- Convert a character to a box-drawing classification -/
def charToBoxChar (c : Char) : Option BoxChar :=
  match c with
  | '╔' => some (.corner true false false false)   -- top-left
  | '╗' => some (.corner false true false false)   -- top-right
  | '╚' => some (.corner false false true false)   -- bottom-left
  | '╝' => some (.corner false false false true)   -- bottom-right
  | '═' => some .horizontal
  | '║' => some .vertical
  | '╦' => some (.junction false true true true)   -- T down
  | '╩' => some (.junction true false true true)   -- T up
  | '╠' => some (.junction true true false true)   -- T right
  | '╣' => some (.junction true true true false)   -- T left
  | '╬' => some (.junction true true true true)    -- cross
  | _ => none

/-- A cell in the 2D grid containing either content or structure -/
inductive TwoDCell where
  /-- Cell containing text content -/
  | content : String → TwoDCell
  /-- Empty cell -/
  | empty : TwoDCell
  /-- Structural cell (box-drawing character) -/
  | structure : BoxChar → TwoDCell
  /-- Cell that spans multiple columns (content continues from previous cell) -/
  | continuation : TwoDCell
  deriving Repr, BEq

instance : Inhabited TwoDCell where
  default := .empty

/-- Convert a cell to display string -/
def TwoDCell.toString : TwoDCell → String
  | .content s => s
  | .empty => ""
  | .structure _ => "□"  -- placeholder for structure display
  | .continuation => "→"

instance : ToString TwoDCell where
  toString := TwoDCell.toString

/-- A row in the 2D grid -/
structure TwoDRow where
  /-- Cells in this row -/
  cells : Array TwoDCell
  /-- Row number -/
  rowNum : Nat
  deriving Repr

/-- A complete 2D grid structure -/
structure TwoDGrid where
  /-- All rows in the grid -/
  rows : Array TwoDRow
  /-- Number of columns (inferred from the widest row) -/
  cols : Nat
  deriving Repr

/-- Get a cell at a specific position, if it exists -/
def TwoDGrid.getCell? (grid : TwoDGrid) (pos : TwoDPosition) : Option TwoDCell :=
  if h : pos.row < grid.rows.size then
    let row := grid.rows[pos.row]'h
    if h2 : pos.col < row.cells.size then
      some row.cells[pos.col]'h2
    else
      none
  else
    none

/-- Set a cell at a specific position -/
def TwoDGrid.setCell (grid : TwoDGrid) (pos : TwoDPosition) (cell : TwoDCell) : TwoDGrid :=
  if h : pos.row < grid.rows.size then
    let oldRow := grid.rows[pos.row]'h
    if h2 : pos.col < oldRow.cells.size then
      let newCells := oldRow.cells.set ⟨pos.col, h2⟩ cell
      let newRow := { oldRow with cells := newCells }
      let newRows := grid.rows.set ⟨pos.row, h⟩ newRow
      { grid with rows := newRows }
    else
      grid  -- Position out of bounds
  else
    grid  -- Position out of bounds

/-- Get the dimensions of the grid -/
def TwoDGrid.dimensions (grid : TwoDGrid) : Nat × Nat :=
  (grid.rows.size, grid.cols)

/-- Check if the grid is well-formed (all rows have the same number of columns) -/
def TwoDGrid.isWellFormed (grid : TwoDGrid) : Bool :=
  grid.rows.all fun row => row.cells.size = grid.cols

/-- Create an empty grid with specified dimensions -/
def TwoDGrid.empty (rows cols : Nat) : TwoDGrid :=
  let emptyRow (rowNum : Nat) : TwoDRow := {
    cells := Array.mkArray cols .empty,
    rowNum := rowNum
  }
  {
    rows := Array.range rows |>.map emptyRow,
    cols := cols
  }

/-- Extract content cells from the grid (ignoring structure) -/
def TwoDGrid.contentCells (grid : TwoDGrid) : Array (TwoDPosition × String) :=
  grid.rows.foldlIdx (init := #[]) fun rowIdx acc row =>
    row.cells.foldlIdx (init := acc) fun colIdx acc2 cell =>
      match cell with
      | .content s => acc2.push (⟨rowIdx, colIdx⟩, s)
      | _ => acc2

/-- Create a simple text-based representation of the grid -/
def TwoDGrid.toText (grid : TwoDGrid) : String :=
  let rowStrings := grid.rows.toList.map fun row =>
    let cellStrings := row.cells.toList.map TwoDCell.toString
    String.intercalate " │ " cellStrings
  String.intercalate "\n" rowStrings

end FuncTracker.TwoD