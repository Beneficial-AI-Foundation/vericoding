import FuncTracker.TwoDSyntax

namespace FuncTracker.TwoD.BoxDrawing

open FuncTracker.TwoD

/-!
# BoxDrawing - Unicode Box-Drawing Character Support

This module provides comprehensive support for Unicode box-drawing characters
used in 2D table syntax. It treats these characters as first-class syntax tokens
rather than ordinary string content.

## Box-Drawing Character Set

We support the standard Unicode box-drawing characters for creating beautiful tables:

```
╔═══╦═══╗  Corners and junctions
║   ║   ║  Vertical lines  
╠═══╬═══╣  Side junctions
║   ║   ║  Vertical lines
╚═══╩═══╝  Bottom corners and junctions
```

## Design Principles

- **Semantic Classification**: Each character has a specific structural meaning
- **Spatial Relationships**: Characters encode connectivity information
- **Validation**: Ensure proper grid structure and connectivity
- **Pretty Generation**: Automatically generate beautiful box-drawing layouts
-/

/-- Comprehensive classification of box-drawing characters with connectivity -/
structure BoxDrawingChar where
  /-- The Unicode character -/
  char : Char
  /-- Connectivity in each direction -/
  connectsUp : Bool
  connectsDown : Bool
  connectsLeft : Bool
  connectsRight : Bool
  /-- Character type classification -/
  charType : BoxChar
  deriving Repr, BEq, DecidableEq

/-- Standard box-drawing character definitions -/
def standardBoxChars : Array BoxDrawingChar := #[
  -- Corners
  { char := '╔', connectsUp := false, connectsDown := true, connectsLeft := false, connectsRight := true, 
    charType := .corner true false false false },
  { char := '╗', connectsUp := false, connectsDown := true, connectsLeft := true, connectsRight := false,
    charType := .corner false true false false },
  { char := '╚', connectsUp := true, connectsDown := false, connectsLeft := false, connectsRight := true,
    charType := .corner false false true false },
  { char := '╝', connectsUp := true, connectsDown := false, connectsLeft := true, connectsRight := false,
    charType := .corner false false false true },
  
  -- Lines
  { char := '═', connectsUp := false, connectsDown := false, connectsLeft := true, connectsRight := true,
    charType := .horizontal },
  { char := '║', connectsUp := true, connectsDown := true, connectsLeft := false, connectsRight := false,
    charType := .vertical },
  
  -- Junctions
  { char := '╦', connectsUp := false, connectsDown := true, connectsLeft := true, connectsRight := true,
    charType := .junction false true true true },
  { char := '╩', connectsUp := true, connectsDown := false, connectsLeft := true, connectsRight := true,
    charType := .junction true false true true },
  { char := '╠', connectsUp := true, connectsDown := true, connectsLeft := false, connectsRight := true,
    charType := .junction true true false true },
  { char := '╣', connectsUp := true, connectsDown := true, connectsLeft := true, connectsRight := false,
    charType := .junction true true true false },
  { char := '╬', connectsUp := true, connectsDown := true, connectsLeft := true, connectsRight := true,
    charType := .junction true true true true }
]

/-- Lookup a box-drawing character definition -/
def findBoxChar (c : Char) : Option BoxDrawingChar :=
  standardBoxChars.find? fun bc => bc.char == c

/-- Check if a character is a box-drawing character -/
def isBoxDrawingChar (c : Char) : Bool :=
  findBoxChar c |>.isSome

/-- Check if a character is a corner character -/
def isCorner (c : Char) : Bool :=
  match findBoxChar c with
  | some bc => match bc.charType with
    | .corner _ _ _ _ => true
    | _ => false
  | none => false

/-- Check if a character is a horizontal line -/
def isHorizontal (c : Char) : Bool :=
  match findBoxChar c with
  | some bc => match bc.charType with
    | .horizontal => true
    | _ => false
  | none => false

/-- Check if a character is a vertical line -/
def isVertical (c : Char) : Bool :=
  match findBoxChar c with
  | some bc => match bc.charType with
    | .vertical => true
    | _ => false
  | none => false

/-- Check if a character is a junction -/
def isJunction (c : Char) : Bool :=
  match findBoxChar c with
  | some bc => match bc.charType with
    | .junction _ _ _ _ => true
    | _ => false
  | none => false

/-- Direction enumeration for connectivity checking -/
inductive Direction where
  | up | down | left | right
  deriving Repr, BEq, DecidableEq

/-- Check if a box-drawing character connects in a given direction -/
def BoxDrawingChar.connects (bc : BoxDrawingChar) (dir : Direction) : Bool :=
  match dir with
  | .up => bc.connectsUp
  | .down => bc.connectsDown
  | .left => bc.connectsLeft
  | .right => bc.connectsRight

/-- Check if two adjacent characters can connect -/
def canConnect (char1 : Char) (dir1 : Direction) (char2 : Char) (dir2 : Direction) : Bool :=
  match findBoxChar char1, findBoxChar char2 with
  | some bc1, some bc2 => bc1.connects dir1 && bc2.connects dir2
  | _, _ => false

/-- Validate that a sequence of horizontal characters forms a valid line -/
def validateHorizontalLine (chars : List Char) : Bool :=
  chars.all isHorizontal

/-- Validate that a sequence of vertical characters forms a valid line -/
def validateVerticalLine (chars : List Char) : Bool :=
  chars.all isVertical

/-- Grid connectivity validation -/
structure GridConnectivity where
  /-- Check horizontal connections between adjacent cells -/
  validateHorizontal : TwoDGrid → TwoDPosition → TwoDPosition → Bool
  /-- Check vertical connections between adjacent cells -/
  validateVertical : TwoDGrid → TwoDPosition → TwoDPosition → Bool

/-- Standard grid connectivity validator -/
def standardGridConnectivity : GridConnectivity where
  validateHorizontal := fun grid pos1 pos2 =>
    if pos1.row == pos2.row && pos1.col + 1 == pos2.col then
      match grid.getCell? pos1, grid.getCell? pos2 with
      | some (.structure bc1), some (.structure bc2) =>
        match findBoxChar bc1.char, findBoxChar bc2.char with
        | some bdc1, some bdc2 => bdc1.connectsRight && bdc2.connectsLeft
        | _, _ => false
      | _, _ => false
    else
      false
  validateVertical := fun grid pos1 pos2 =>
    if pos1.col == pos2.col && pos1.row + 1 == pos2.row then
      match grid.getCell? pos1, grid.getCell? pos2 with
      | some (.structure bc1), some (.structure bc2) =>
        match findBoxChar bc1.char, findBoxChar bc2.char with
        | some bdc1, some bdc2 => bdc1.connectsDown && bdc2.connectsUp
        | _, _ => false
      | _, _ => false
    else
      false

/-- Generate appropriate box-drawing character for a position -/
def generateBoxChar (connectsUp connectsDown connectsLeft connectsRight : Bool) : Option Char :=
  standardBoxChars.find? fun bc =>
    bc.connectsUp == connectsUp && 
    bc.connectsDown == connectsDown && 
    bc.connectsLeft == connectsLeft && 
    bc.connectsRight == connectsRight
  |>.map (·.char)

/-- Automatically generate a beautiful table border -/
def generateTableBorder (width height : Nat) : Array (Array Char) :=
  let generateRow (rowIdx : Nat) : Array Char :=
    Array.range width |>.map fun colIdx =>
      if rowIdx == 0 then
        -- Top row
        if colIdx == 0 then '╔'
        else if colIdx == width - 1 then '╗'
        else '═'
      else if rowIdx == height - 1 then
        -- Bottom row  
        if colIdx == 0 then '╚'
        else if colIdx == width - 1 then '╝'
        else '═'
      else
        -- Middle rows
        if colIdx == 0 || colIdx == width - 1 then '║'
        else ' '
  
  Array.range height |>.map generateRow

/-- Format a table with proper box-drawing characters -/
def formatTable (content : Array (Array String)) (colWidths : Array Nat) : String :=
  if content.isEmpty || colWidths.isEmpty then
    ""
  else
    let totalWidth := colWidths.foldl (· + ·) 0 + colWidths.size + 1
    let height := content.size + 2  -- +2 for top and bottom borders
    
    -- Generate border template
    let borders := generateTableBorder totalWidth height
    
    -- Create formatted rows
    let rows := content.toList.mapIdx fun rowIdx row =>
      let cells := row.toList.zip colWidths.toList |>.map fun (cell, width) =>
        let padded := cell.take width.toNat
        padded ++ String.mk (List.replicate (width.toNat - padded.length) ' ')
      "║" ++ String.intercalate "║" cells ++ "║"
    
    -- Combine with borders
    let topBorder := String.mk borders[0]!.toList
    let bottomBorder := String.mk borders[height - 1]!.toList
    
    String.intercalate "\n" ([topBorder] ++ rows ++ [bottomBorder])

/-- Pretty-print a 2D grid with proper box-drawing -/
def prettyPrintGrid (grid : TwoDGrid) : String :=
  let contentRows := grid.rows.toList.map fun row =>
    row.cells.toList.map fun cell =>
      match cell with
      | .content s => s
      | .empty => ""
      | .structure bc => bc.char.toString
      | .continuation => "→"
  
  let rowStrings := contentRows.map fun row =>
    String.intercalate "" row
  
  String.intercalate "\n" rowStrings

end FuncTracker.TwoD.BoxDrawing