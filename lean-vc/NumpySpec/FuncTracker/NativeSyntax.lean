import Lean

namespace FuncTracker.NativeSyntax

open Lean

/-!
# NativeSyntax - True Native 2D Token Registration

This module implements **true native 2D syntax** where box-drawing characters
are recognized as first-class syntax tokens by Lean's lexer, not parsed from strings.

This is the foundation for implementing Racket-style `#2d` syntax in Lean 4.

## Key Innovation

Instead of parsing strings like:
```lean
simpleTable2d "╔═══╗\n║...║\n╚═══╝"  -- String-based ❌
```

We register Unicode box-drawing characters as **actual syntax tokens**:
```lean
funcTable2d
╔═══════════════╦═══════════╗
║ Function      ║ Status    ║  -- These are tokens! ✅
╠═══════════════╬═══════════╣
║ List.map      ║ ✓✓✓       ║
╚═══════════════╩═══════════╝
```

## Design Philosophy

- **Token-First**: Box-drawing characters are lexer tokens, not string content
- **Spatial Awareness**: Preserve 2D relationships in syntax tree structure  
- **Type Safety**: Maintain all Lean guarantees while adding 2D syntax
- **Performance**: No string parsing overhead, direct syntax tree processing
-/

-- =============================================================================
-- BOX-DRAWING CHARACTER TOKEN REGISTRATION
-- =============================================================================

/-- Corner tokens for table borders -/
syntax "╔" : box_corner_tl  -- Top-left corner
syntax "╗" : box_corner_tr  -- Top-right corner
syntax "╚" : box_corner_bl  -- Bottom-left corner  
syntax "╝" : box_corner_br  -- Bottom-right corner

/-- Line tokens for table structure -/
syntax "║" : box_vertical    -- Vertical line
syntax "═" : box_horizontal  -- Horizontal line

/-- Junction tokens for table intersections -/
syntax "╦" : box_junction_t  -- T-junction pointing down
syntax "╩" : box_junction_b  -- T-junction pointing up
syntax "╠" : box_junction_l  -- T-junction pointing right
syntax "╣" : box_junction_r  -- T-junction pointing left
syntax "╬" : box_junction_x  -- Cross junction

-- =============================================================================
-- STATUS SYMBOL TOKEN REGISTRATION
-- =============================================================================

/-- Status tokens for function progress -/
syntax "✗" : status_not_started
syntax "⋯" : status_in_progress  
syntax "✓" : status_implemented
syntax "✓✓" : status_tested
syntax "✓✓✓" : status_documented

-- =============================================================================
-- SYNTAX CATEGORIES FOR 2D STRUCTURE
-- =============================================================================

/-- Main category for 2D table content -/
declare_syntax_cat table_2d

/-- Category for table rows -/
declare_syntax_cat table_row

/-- Category for table cells -/
declare_syntax_cat table_cell

/-- Category for table borders -/
declare_syntax_cat table_border

/-- Category for table separators -/
declare_syntax_cat table_separator

-- =============================================================================
-- CELL CONTENT SYNTAX RULES
-- =============================================================================

/-- Function names as cell content -/
syntax ident : table_cell

/-- String literals as cell content -/
syntax str : table_cell

/-- File paths (often contain dots) -/
syntax ident "." ident : table_cell  -- Simple dotted names like "List.lean"

/-- Status symbols as cell content -/
syntax status_not_started : table_cell
syntax status_in_progress : table_cell  
syntax status_implemented : table_cell
syntax status_tested : table_cell
syntax status_documented : table_cell

/-- Empty cell marker -/
syntax "-" : table_cell

/-- Whitespace in cells (for alignment) -/
syntax:max " " : table_cell

-- =============================================================================
-- BORDER SYNTAX RULES  
-- =============================================================================

/-- Top border pattern: ╔═══╦═══╗ -/
syntax box_corner_tl box_horizontal* (box_junction_t box_horizontal*)* box_corner_tr : table_border

/-- Bottom border pattern: ╚═══╩═══╝ -/
syntax box_corner_bl box_horizontal* (box_junction_b box_horizontal*)* box_corner_br : table_border

/-- Separator pattern: ╠═══╬═══╣ -/
syntax box_junction_l box_horizontal* (box_junction_x box_horizontal*)* box_junction_r : table_separator

-- =============================================================================
-- ROW SYNTAX RULES
-- =============================================================================

/-- Table row pattern: ║ cell ║ cell ║ -/
syntax box_vertical table_cell* (box_vertical table_cell*)* box_vertical : table_row

-- =============================================================================
-- COMPLETE TABLE SYNTAX
-- =============================================================================

/-- Complete 2D table with spatial awareness -/
syntax (name := nativeTable2d) "funcTable2d" withPosition(
  checkColGe table_border linebreak+
  checkColGe table_row linebreak+  
  checkColGe table_separator linebreak+
  checkColGe sepBy1(table_row, linebreak+)
  checkColGe table_border
) : term

-- =============================================================================
-- HELPER SYNTAX FOR GRADUAL TRANSITION
-- =============================================================================

/-- Simpler table syntax for testing (fewer requirements) -/
syntax (name := simpleNativeTable2d) "simpleNative2d" withPosition(
  checkColGe table_border linebreak
  checkColGe table_row linebreak  
  checkColGe table_border
) : term

-- =============================================================================
-- TOKEN CLASSIFICATION UTILITIES
-- =============================================================================

/-- Check if a syntax node represents a box-drawing character -/
def isBoxDrawingSyntax (stx : Syntax) : Bool :=
  match stx.getKind with
  | `box_corner_tl | `box_corner_tr | `box_corner_bl | `box_corner_br => true
  | `box_vertical | `box_horizontal => true
  | `box_junction_t | `box_junction_b | `box_junction_l | `box_junction_r | `box_junction_x => true
  | _ => false

/-- Check if a syntax node represents a status symbol -/
def isStatusSyntax (stx : Syntax) : Bool :=
  match stx.getKind with
  | `status_not_started | `status_in_progress | `status_implemented => true
  | `status_tested | `status_documented => true
  | _ => false

/-- Extract semantic meaning from box-drawing syntax -/
def getBoxSemantics (stx : Syntax) : Option String :=
  match stx.getKind with
  | `box_corner_tl => some "top-left"
  | `box_corner_tr => some "top-right" 
  | `box_corner_bl => some "bottom-left"
  | `box_corner_br => some "bottom-right"
  | `box_vertical => some "vertical"
  | `box_horizontal => some "horizontal"
  | `box_junction_t => some "junction-down"
  | `box_junction_b => some "junction-up"
  | `box_junction_l => some "junction-right"
  | `box_junction_r => some "junction-left"
  | `box_junction_x => some "junction-cross"
  | _ => none

/-- Extract status from status syntax -/
def getStatusSemantics (stx : Syntax) : Option String :=
  match stx.getKind with
  | `status_not_started => some "not-started"
  | `status_in_progress => some "in-progress"
  | `status_implemented => some "implemented"
  | `status_tested => some "tested"
  | `status_documented => some "documented"
  | _ => none

-- =============================================================================
-- SYNTAX TREE ANALYSIS UTILITIES
-- =============================================================================

/-- Count occurrences of a specific syntax kind in a syntax tree -/
def countSyntaxKind (stx : Syntax) (kind : SyntaxKind) : Nat :=
  let rec count (s : Syntax) : Nat :=
    let selfCount := if s.getKind == kind then 1 else 0
    let childCount := s.getArgs.foldl (fun acc child => acc + count child) 0
    selfCount + childCount
  count stx

/-- Extract all syntax nodes of a specific kind from a syntax tree -/
def extractSyntaxKind (stx : Syntax) (kind : SyntaxKind) : Array Syntax :=
  let rec extract (s : Syntax) (acc : Array Syntax) : Array Syntax :=
    let newAcc := if s.getKind == kind then acc.push s else acc
    s.getArgs.foldl extract newAcc
  extract stx #[]

/-- Analyze table structure from border syntax -/
def analyzeBorderStructure (borderStx : Syntax) : Nat × Nat :=
  let horizontalCount := countSyntaxKind borderStx `box_horizontal
  let junctionCount := countSyntaxKind borderStx `box_junction_t + 
                      countSyntaxKind borderStx `box_junction_b +
                      countSyntaxKind borderStx `box_junction_x
  let columnCount := junctionCount + 1
  (columnCount, horizontalCount)

/-- Extract cell content from table row syntax -/
def extractCellNodes (rowStx : Syntax) : Array Syntax :=
  -- Find all non-vertical-bar syntax nodes in the row
  let allNodes := rowStx.getArgs
  allNodes.filter (fun node => node.getKind != `box_vertical)

-- =============================================================================
-- VALIDATION UTILITIES
-- =============================================================================

/-- Validate that a table border has consistent structure -/
def validateBorderConsistency (topBorder bottomBorder : Syntax) : Bool :=
  let (topCols, topHoriz) := analyzeBorderStructure topBorder
  let (bottomCols, bottomHoriz) := analyzeBorderStructure bottomBorder
  topCols == bottomCols && topHoriz == bottomHoriz

/-- Validate that all rows have consistent column count -/
def validateRowConsistency (rows : Array Syntax) (expectedCols : Nat) : Bool :=
  rows.all fun row =>
    let cellCount := (extractCellNodes row).size
    cellCount == expectedCols

-- =============================================================================
-- DEBUGGING AND INSPECTION UTILITIES
-- =============================================================================

/-- Pretty-print syntax tree structure for debugging -/
def inspectSyntaxTree (stx : Syntax) (depth : Nat := 0) : String :=
  let indent := String.mk (List.replicate (depth * 2) ' ')
  let kindStr := stx.getKind.toString
  let argsStr := if stx.getArgs.isEmpty then ""
    else "\n" ++ String.intercalate "\n" (stx.getArgs.toList.map (inspectSyntaxTree · (depth + 1)))
  s!"{indent}{kindStr}{argsStr}"

/-- Extract raw text from syntax for comparison -/
def syntaxToText (stx : Syntax) : String :=
  match stx with
  | .atom _ text => text
  | .ident _ _ text _ => text.toString
  | .node _ _ args => String.intercalate " " (args.toList.map syntaxToText)
  | _ => s!"<{stx.getKind}>"

/-- Count total tokens in a syntax tree -/
def countTokens (stx : Syntax) : Nat :=
  let rec count (s : Syntax) : Nat :=
    let selfCount := if s.isAtom || s.isIdent then 1 else 0
    let childCount := s.getArgs.foldl (fun acc child => acc + count child) 0
    selfCount + childCount
  count stx

end FuncTracker.NativeSyntax