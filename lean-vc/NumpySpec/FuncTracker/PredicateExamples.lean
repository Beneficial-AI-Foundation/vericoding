import FuncTracker.BasicV2
import FuncTracker.SimpleValidation
import FuncTracker.RegionPredicates

namespace FuncTracker.PredicateExamples

open FuncTracker

/-- Example table for testing predicates -/
def exampleTable := funcTable! "╔═══════════════════════════════════════════════════════════════╗
│ Name                 │ Status │ File       │ Lines     │ Complexity │
╠═══════════════════════════════════════════════════════════════╣
│ List.map             │ ✓✓✓    │ List.lean  │ 100-120   │ O(n)       │
│ Array.map            │ ✓✓     │ Array.lean │ 50-80     │ -          │
│ Option.map           │ ✓      │ -          │ -         │ -          │
│ Nat.add              │ ✗      │ -          │ -         │ -          │
╚═══════════════════════════════════════════════════════════════╝"

-- Test individual predicates

/-- Test: All documented functions should have complexity info -/
def testDocumentedHasComplexity : IO Unit := do
  match exampleTable.wholeRegion with
  | some wholeTable =>
    let predicate := testedHasComplexity
    let result := validateTableRegion exampleTable predicate wholeTable
    match result with
    | .success => IO.println "✓ All tested functions have complexity info"
    | .failure msg pos => IO.println s!"✗ Validation failed: {msg} at {pos}"
  | none => IO.println "✗ Could not create table region"

/-- Test: Status column should have at least "in progress" for active development -/
def testStatusColumn : IO Unit := do
  let statusCol := exampleTable.columnRegion 1  -- Status is column 1
  match statusCol with
  | some region =>
    let predicate := statusAtLeast .inProgress
    let result := validateTableRegion exampleTable predicate region
    match result with
    | .success => IO.println "✓ All functions have progress status"
    | .failure msg pos => IO.println s!"✗ Status check failed: {msg} at {pos}"
  | none => IO.println "✗ Could not create status column region"

/-- Test: Combine multiple predicates with AND -/
def testCombinedPredicates : IO Unit := do
  match exampleTable.wholeRegion with
  | some wholeTable =>
    let combinedPredicate := (statusAtLeast .notStarted).and testedHasComplexity
    let result := validateTableRegion exampleTable combinedPredicate wholeTable
    match result with
    | .success => IO.println "✓ Combined validation passed"
    | .failure msg pos => IO.println s!"✗ Combined validation failed: {msg} at {pos}"
  | none => IO.println "✗ Could not create table region"

/-- Custom predicate: implemented functions should have file info -/
def implementedHasFile : RegionPredicate :=
  cellPredicate fun func pos =>
    if func.status ≥ .implemented then
      match func.file with
      | some _ => .success
      | none => .failure s!"Function {func.name} is implemented but missing file info" (some pos)
    else
      .success

/-- Test the custom predicate -/
def testImplementedHasFile : IO Unit := do
  match exampleTable.wholeRegion with
  | some wholeTable =>
    let result := validateTableRegion exampleTable implementedHasFile wholeTable
    match result with
    | .success => IO.println "✓ All implemented functions have file info"
    | .failure msg pos => IO.println s!"✗ File info check failed: {msg} at {pos}"
  | none => IO.println "✗ Could not create table region"

/-- Example of compositional predicate building -/
def comprehensiveValidation : RegionPredicate :=
  (statusAtLeast .notStarted).and
  (testedHasComplexity.and implementedHasFile)

/-- Test the comprehensive validation -/
def testComprehensive : IO Unit := do
  match exampleTable.wholeRegion with
  | some wholeTable =>
    let result := validateTableRegion exampleTable comprehensiveValidation wholeTable
    match result with
    | .success => IO.println "✓ Comprehensive validation passed"
    | .failure msg pos => IO.println s!"✗ Comprehensive validation failed: {msg} at {pos}"
  | none => IO.println "✗ Could not create table region"

/-- Example of region-specific validation -/
def testTopTwoRows : IO Unit := do
  -- Create a region for just the first two function rows
  let topRegion : Region := ⟨0, 0, 1, 4, by simp⟩
  let predicate := statusAtLeast .implemented
  let result := validateTableRegion exampleTable predicate topRegion
  match result with
  | .success => IO.println "✓ Top two functions are implemented"
  | .failure msg pos => IO.println s!"✗ Top two functions check failed: {msg} at {pos}"

-- Run all tests
#eval testDocumentedHasComplexity
#eval testStatusColumn  
#eval testCombinedPredicates
#eval testImplementedHasFile
#eval testComprehensive
#eval testTopTwoRows

/-- Demo: Building predicates compositionally like parser combinators -/
namespace CompositionDemo

-- Build a validation suite step by step
def basicChecks := statusAtLeast .notStarted
def fileChecks := implementedHasFile  
def complexityChecks := testedHasComplexity

-- Compose them functorially
def level1Validation := basicChecks.and fileChecks
def level2Validation := level1Validation.and complexityChecks

-- This demonstrates the same compositional approach as our parser:
-- Start with atomic components, build larger structures functorially

def validateDevelopmentStandards (table : FunctionTable) : PredicateResult :=
  match table.wholeRegion with
  | some region => validateTableRegion table level2Validation region
  | none => .failure "Empty table" none

#eval do
  let result := validateDevelopmentStandards exampleTable
  match result with
  | .success => IO.println "✓ Development standards met"
  | .failure msg pos => IO.println s!"✗ Standards validation: {msg} at {pos}"

end CompositionDemo

end FuncTracker.PredicateExamples