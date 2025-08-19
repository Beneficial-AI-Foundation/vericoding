import FuncTracker.BasicV2
import FuncTracker.GridParserV2

namespace FuncTracker

/-!
# Region Predicates

Compositional predicate checking for table regions.
Build complex semantic validation from simple predicate combinators.

## Design Philosophy
Follow the same compositional approach as the parser:
- Define atomic predicates for single cells
- Build combinators for region operations  
- Compose complex validation rules functorially
- Provide precise error localization
-/

/-- A rectangular region in the table with coordinates -/
structure Region where
  /-- Top-left row (0-indexed) -/
  startRow : Nat
  /-- Top-left column (0-indexed) -/
  startCol : Nat
  /-- Bottom-right row (0-indexed, inclusive) -/
  endRow : Nat
  /-- Bottom-right column (0-indexed, inclusive) -/
  endCol : Nat
  /-- Ensure region is well-formed -/
  valid : startRow ≤ endRow ∧ startCol ≤ endCol
  deriving Repr

/-- A position in the table -/
structure Position where
  /-- Row coordinate -/
  row : Nat
  /-- Column coordinate -/
  col : Nat
  deriving Repr, BEq, Ord

instance : ToString Position where
  toString pos := s!"({pos.row}, {pos.col})"

/-- Check if a position is within a region -/
def Position.inRegion (pos : Position) (region : Region) : Bool :=
  region.startRow ≤ pos.row ∧ pos.row ≤ region.endRow ∧
  region.startCol ≤ pos.col ∧ pos.col ≤ region.endCol

/-- Get all positions within a region -/
def Region.positions (region : Region) : List Position :=
  let rows := List.range (region.endRow - region.startRow + 1) |>.map (· + region.startRow)
  let cols := List.range (region.endCol - region.startCol + 1) |>.map (· + region.startCol)
  rows.flatMap fun r => cols.map fun c => ⟨r, c⟩

/-- A predicate validation result -/
inductive PredicateResult where
  /-- Predicate succeeded -/
  | success : PredicateResult
  /-- Predicate failed with message and optional position -/
  | failure (message : String) (position : Option Position := none) : PredicateResult
  deriving Repr

/-- Check if a predicate result is success -/
def PredicateResult.isSuccess : PredicateResult → Bool
  | .success => true
  | .failure _ _ => false

/-- Combine predicate results -/
def PredicateResult.and (r1 r2 : PredicateResult) : PredicateResult :=
  match r1, r2 with
  | .success, .success => .success
  | .failure msg pos, .success => .failure msg pos
  | .success, .failure msg pos => .failure msg pos
  | .failure msg1 pos1, .failure msg2 pos2 => 
    .failure s!"{msg1}; {msg2}" (pos1 <|> pos2)

/-- A predicate that can be applied to a table region -/
structure RegionPredicate where
  /-- Apply the predicate to a function table and region -/
  check : FunctionTable → Region → PredicateResult

/-- Atomic predicate: check a single cell property -/
def cellPredicate (check : TrackedFunction → Position → PredicateResult) : RegionPredicate :=
  ⟨fun table region =>
    let results := region.positions.map fun pos =>
      if h : pos.row < table.functions.size then
        let func := table.functions[pos.row]'h
        check func pos
      else
        .failure s!"Position {pos} out of bounds" (some pos)
    results.foldl PredicateResult.and .success⟩

/-- Atomic predicate: status must be at least the given level -/
def statusAtLeast (minStatus : Status) : RegionPredicate :=
  cellPredicate fun func pos =>
    if func.status ≥ minStatus then
      .success
    else
      .failure s!"Function {func.name} has status {func.status.toSymbol} but expected at least {minStatus.toSymbol}" (some pos)

/-- Atomic predicate: function name must exist (already checked by elaborator, but for demo) -/
def nameExists : RegionPredicate :=
  cellPredicate fun func pos =>
    -- In practice, this would check environment, but names are already validated
    .success

/-- Atomic predicate: if status is tested, complexity should be specified -/
def testedHasComplexity : RegionPredicate :=
  cellPredicate fun func pos =>
    if func.status ≥ .tested then
      match func.complexity with
      | some _ => .success
      | none => .failure s!"Function {func.name} is tested but missing complexity info" (some pos)
    else
      .success

/-- Combinator: logical AND of two predicates -/
def RegionPredicate.and (p1 p2 : RegionPredicate) : RegionPredicate :=
  ⟨fun table region =>
    let r1 := p1.check table region
    let r2 := p2.check table region
    r1.and r2⟩

/-- Combinator: logical OR of two predicates -/
def RegionPredicate.or (p1 p2 : RegionPredicate) : RegionPredicate :=
  ⟨fun table region =>
    let r1 := p1.check table region
    match r1 with
    | .success => .success
    | .failure _ _ => p2.check table region⟩

/-- Combinator: logical NOT of a predicate -/
def RegionPredicate.not (p : RegionPredicate) : RegionPredicate :=
  ⟨fun table region =>
    match p.check table region with
    | .success => .failure "Predicate should have failed" none
    | .failure _ _ => .success⟩

/-- Combinator: predicate must hold for all positions in region -/
def RegionPredicate.forall (p : RegionPredicate) : RegionPredicate := p

/-- Combinator: predicate must hold for at least one position in region -/
def RegionPredicate.exists (p : RegionPredicate) : RegionPredicate :=
  ⟨fun table region =>
    let results := region.positions.map fun pos =>
      let singleRegion : Region := ⟨pos.row, pos.col, pos.row, pos.col, by simp⟩
      p.check table singleRegion
    if results.any PredicateResult.isSuccess then .success
    else .failure "Predicate failed for all positions in region" none⟩

/-- Helper: create a region for the entire table -/
def FunctionTable.wholeRegion (table : FunctionTable) : Option Region :=
  if table.functions.isEmpty then none
  else 
    -- Assume we have columns: Name, Status, File, etc. (let's say 5 columns)
    let numCols := 5  -- This should be computed from actual table structure
    some ⟨0, 0, table.functions.size - 1, numCols - 1, by simp⟩

/-- Helper: create a region for a specific column -/
def FunctionTable.columnRegion (table : FunctionTable) (col : Nat) : Option Region :=
  if table.functions.isEmpty then none
  else some ⟨0, col, table.functions.size - 1, col, by simp⟩

/-- Helper: create a region for a specific row -/  
def FunctionTable.rowRegion (table : FunctionTable) (row : Nat) : Option Region :=
  if h : row < table.functions.size then
    some ⟨row, 0, row, 4, by simp⟩  -- Assume 5 columns (0-4)
  else none

/-- Validate a table using a predicate and region -/
def validateTableRegion (table : FunctionTable) (predicate : RegionPredicate) (region : Region) : PredicateResult :=
  predicate.check table region

-- Infix operators for predicate combinators
instance : HAnd RegionPredicate RegionPredicate RegionPredicate where
  hAnd := RegionPredicate.and

instance : HOr RegionPredicate RegionPredicate RegionPredicate where
  hOr := RegionPredicate.or

end FuncTracker