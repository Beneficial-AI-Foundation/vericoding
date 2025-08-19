import Lean
import Std.Internal.Parsec
import FuncTracker.BasicV2

namespace FuncTracker

open Std.Internal.Parsec
open Std.Internal.Parsec.String

/-- A cell in the 2D grid -/
inductive GridCell where
  | content : String → GridCell
  | border : Char → GridCell
  | empty : GridCell
  deriving Repr

/-- A 2D grid structure -/
structure Grid where
  cells : Array (Array String)
  rows : Nat
  cols : Nat
  deriving Repr

namespace GridParser

-- Import all the parser combinators from GridParser.lean
/-- Parse whitespace -/
def ws : Parser Unit := do
  let _ ← many (satisfy (fun c => c == ' ' || c == '\t'))
  pure ()

/-- Parse many characters satisfying a predicate -/
def manyChars (p : Char → Bool) : Parser String := do
  let chars ← many (satisfy p)
  return String.mk chars.toList

/-- Parse many1 characters satisfying a predicate -/
def many1Chars (p : Char → Bool) : Parser String := do
  let chars ← many1 (satisfy p)
  return String.mk chars.toList

/-- Parse a specific character -/
def pchar (c : Char) : Parser Char := 
  satisfy (· == c)

/-- Parse horizontal border line: ═══ -/
def hBorder : Parser Unit := do
  let _ ← many1 (pchar '═')
  pure ()

/-- Parse top border: ╔═══╗ -/
def topBorder : Parser Unit := do
  let _ ← pchar '╔'
  let _ ← hBorder
  let _ ← pchar '╗'
  let _ ← optional (pchar '\n')
  pure ()

/-- Parse bottom border: ╚═══╝ -/
def bottomBorder : Parser Unit := do
  let _ ← pchar '╚'
  let _ ← hBorder
  let _ ← pchar '╝'
  -- Don't consume anything after the border
  pure ()

/-- Parse separator border: ╠═══╣ -/
def separatorBorder : Parser Unit := do
  let _ ← pchar '╠'
  let _ ← hBorder
  let _ ← pchar '╣'
  let _ ← optional (pchar '\n')
  pure ()

/-- Parse cell content between │ separators -/
def cellContent : Parser String := do
  let chars ← manyChars (fun c => c != '│' && c != '\n')
  pure chars.trim

/-- Parse at least one non-empty cell content -/
def cellContentNonEmpty : Parser String := do
  let content ← cellContent
  if content.isEmpty then
    fail "empty cell"
  else
    pure content

/-- Manual implementation of sepBy1 -/
def sepBy1Core (sep : Parser α) (p : Parser β) : Parser (List β) := do
  let first ← p
  let rest ← many (sep *> p)
  return first :: rest.toList

/-- Parse cells between bars: returns array of cell contents -/
def parseCellsBetweenBars (s : String) : Array String :=
  -- Split by │ and take the parts between the bars
  let parts := s.splitOn "│"
  -- Remove first and last empty parts, trim the rest
  if parts.length ≥ 2 then
    let middle : List String := parts.drop 1 |>.take (parts.length - 2)
    middle.map String.trim |>.toArray
  else
    #[]

/-- Skip a specific character -/
def skip (c : Char) : Parser Unit := 
  pchar c *> pure ()

/-- Skip optional whitespace -/  
def skipWs : Parser Unit :=
  ws

/-- Parse text up to a delimiter (non-inclusive) -/
def textUpto (delim : Char) : Parser String :=
  manyChars (· != delim)

/-- Parse text between two characters -/
def betweenChars (openChar closeChar : Char) (p : Parser α) : Parser α := do
  let _ ← skip openChar
  let result ← p
  let _ ← skip closeChar
  return result

/-- Parse a single table cell (without bars) -/
def parseCell : Parser String := do
  let content ← textUpto '│'
  return content.trim

/-- Parse one bar followed by one cell -/
def barCell : Parser String := do
  let _ ← skip '│'
  let _ ← skipWs
  let cell ← parseCell
  let _ ← skipWs
  -- Fail if cell is empty (which means we hit another bar immediately)
  if cell.isEmpty then
    fail "empty cell"
  else
    return cell

/-- Parse a table row: │ cell │ cell │ -/  
def tableRow : Parser (Array String) := do
  -- Strategy: parse the whole line, then split by │
  let line ← manyChars (· != '\n')
  -- Validate it starts and ends with │
  if !line.startsWith "│" || !line.endsWith "│" then
    fail "row must start and end with │"
  -- Split and extract cells
  let cells := parseCellsBetweenBars line
  if cells.isEmpty then
    fail "empty row"
  return cells

/-- Parse complete table -/
def parseTable : Parser Grid := do
  -- Top border
  let _ ← topBorder
  
  -- Parse all rows
  let mut allRows : Array (Array String) := #[]
  let mut foundSeparator := false
  
  repeat
    -- Check what's next without consuming
    match ← optional (attempt tableRow) with
    | some cells =>
      -- Successfully parsed a data row
      allRows := allRows.push cells
      let _ ← optional (pchar '\n')
    | none =>
      -- Not a data row, check if it's a separator or bottom
      match ← optional (attempt separatorBorder) with
      | some _ =>
        -- It's a separator
        foundSeparator := true
      | none =>
        -- Must be bottom border, exit loop
        break
  
  -- Parse bottom border
  let _ ← bottomBorder
  
  -- Validate dimensions
  if allRows.size == 0 then
    fail "empty table"
  
  let cols := allRows[0]!.size
  for row in allRows do
    if row.size != cols then
      fail s!"inconsistent row width: expected {cols}, got {row.size}"
  
  return { 
    cells := allRows
    rows := allRows.size
    cols := cols
  }

/-- Run parser on a string -/
def run (input : String) : Except String Grid :=
  match parseTable input.mkIterator with
  | .success _ res => .ok res
  | .error it msg => .error s!"Parse error at position {repr it.i}: {msg}"

end GridParser

/-- Convert grid to FunctionTable with Names -/
def gridToFunctionTableV2 (grid : Grid) : Except String FunctionTable := do
  let mut functions : Array TrackedFunction := #[]
  
  for row in grid.cells do
    if row.size < 2 then
      throw "Row must have at least name and status columns"
    
    let nameStr := row[0]!
    let statusStr := row[1]!
    
    -- Convert string to Name
    let name := stringToName nameStr
    
    let status ← match statusStr with
      | "✗" => pure Status.notStarted
      | "⋯" => pure Status.inProgress
      | "✓" => pure Status.implemented
      | "✓✓" => pure Status.tested
      | "✓✓✓" => pure Status.documented
      | _ => throw s!"Invalid status symbol: {statusStr}"
    
    let file := if h : row.size > 2 then
      let f := row[2]
      if f == "-" || f == "" then none else some f
    else none
    
    let lines := if h : row.size > 3 then
      let l := row[3]
      if l == "-" || l == "" then none
      else
        -- Parse "10-20" format
        let parts := l.splitOn "-"
        if parts.length == 2 then
          match parts[0]!.toNat?, parts[1]!.toNat? with
          | some start, some «end» => some (start, «end»)
          | _, _ => none
        else none
    else none
    
    let complexity := if h : row.size > 4 then
      let c := row[4]
      if c == "-" || c == "" then none else some c
    else none
    
    -- Extract cross-refs from a "refs" column if present (column 5, index 4)
    let refs := if h : row.size > 4 then
      -- Check if this is actually refs or complexity
      let col := row[4]
      if col.contains ',' || col.contains '.' then
        -- Likely refs (contains dots or commas)
        let refStrs := col.splitOn ","
        refStrs.map (fun s => stringToName s.trim) |>.toArray
      else
        #[]
    else if h : row.size > 5 then
      let r := row[5]
      if r == "-" || r == "" then #[]
      else
        -- Parse comma-separated refs
        let refStrs := r.splitOn ","
        refStrs.map (fun s => stringToName s.trim) |>.toArray
    else #[]
    
    functions := functions.push {
      name := name
      status := status
      file := file
      lines := lines
      complexity := complexity
      docString := none  -- Would be filled by Verso integration
      refs := refs
    }
  
  return { functions := functions }

end FuncTracker