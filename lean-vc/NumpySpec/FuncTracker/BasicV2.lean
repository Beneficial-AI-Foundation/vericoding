import Lean

namespace FuncTracker

open Lean

/-- Status of a function implementation -/
inductive Status where
  /-- The function has not been started. -/
  | notStarted
  /-- The function is in progress. -/
  | inProgress
  /-- The function is implemented. -/
  | implemented
  /-- The function is tested. -/
  | tested
  /-- The function is documented. -/
  | documented
  deriving Repr, DecidableEq, BEq

/-- Convert a status to a symbol for display -/
def Status.toSymbol : Status → String
  | .notStarted => "✗"
  | .inProgress => "⋯"
  | .implemented => "✓"
  | .tested => "✓✓"
  | .documented => "✓✓✓"

/-- Convert a status to a number for comparison -/
def Status.toNat : Status → Nat
  | .notStarted => 0
  | .inProgress => 1
  | .implemented => 2
  | .tested => 3
  | .documented => 4

/-- Status has a natural ordering: notStarted < inProgress < implemented < tested < documented -/
instance : LE Status where
  le s1 s2 := s1.toNat ≤ s2.toNat

instance : LT Status where
  lt s1 s2 := s1.toNat < s2.toNat

instance : DecidableRel (· ≤ · : Status → Status → Prop) := 
  fun a b => inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

/-- Reference type for cross-references -/
inductive ReferenceType where
  | dependsOn    -- This function depends on the referenced function
  | implements   -- This function implements the referenced interface/spec
  | tests        -- This function tests the referenced function
  | documents    -- This function documents the referenced function
  | calls        -- This function calls the referenced function
  | implementedBy -- This function is implemented by the referenced function
  deriving Repr, BEq, DecidableEq

/-- Convert ReferenceType to string -/
def ReferenceType.toString : ReferenceType → String
  | .dependsOn => "depends-on"
  | .implements => "implements"
  | .tests => "tests"
  | .documents => "documents"
  | .calls => "calls"
  | .implementedBy => "implemented-by"

instance : ToString ReferenceType where
  toString := ReferenceType.toString

/-- A typed cross-reference with additional metadata -/
structure CrossReference where
  /-- The referenced function name -/
  target : Name
  /-- Type of the reference relationship -/
  refType : ReferenceType
  /-- Optional note about the relationship -/
  note : Option String := none
  deriving Repr, BEq, DecidableEq

/-- A tracked function with its implementation status -/
structure TrackedFunction where
  /-- Name of the function as a Lean Name -/
  name : Name
  /-- Status of the function implementation -/
  status : Status
  /-- File containing the function implementation, if known. -/
  file : Option String := none
  /-- Line range of the function implementation, if known. Row, column indices. -/
  lines : Option (Nat × Nat) := none
  /-- Complexity of the function, if known. -/
  complexity : Option String := none
  /-- Documentation string from Verso, if available -/
  docString : Option String := none
  /-- URL to Verso documentation, if available -/
  versoLink : Option String := none
  /-- Cross-references to related functions (legacy - use typedRefs for new code) -/
  refs : Array Name := #[]
  /-- Typed cross-references with relationship information -/
  typedRefs : Array CrossReference := #[]
  /-- Version or commit hash when this entry was last updated -/
  version : Option String := none
  deriving Repr, BEq, DecidableEq

/-- Convert string to Name, handling module paths -/
def stringToName (s : String) : Name :=
  -- Split by dots for module paths like "Lean.Parser.parseTable"
  let parts := s.splitOn "."
  parts.foldl (init := Name.anonymous) fun acc part =>
    acc.str part

/-- Table data structure -/
structure FunctionTable where
  /-- Array of tracked functions -/
  functions : Array TrackedFunction
  /-- Module this table is tracking -/
  module : Option Name := none
  deriving Repr, BEq, DecidableEq

/-- Progress statistics -/
structure Progress where
  /-- Total number of functions in the table. -/
  total : Nat
  /-- Number of functions that have not been started. -/
  notStarted : Nat
  /-- Number of functions that are in progress. -/
  inProgress : Nat
  /-- Number of functions that are implemented. -/
  implemented : Nat
  /-- Number of functions that are tested. -/
  tested : Nat
  /-- Number of functions that are documented. -/
  documented : Nat
  deriving Repr, BEq, DecidableEq

/-- Compute the progress of a function table -/
def FunctionTable.computeProgress (table : FunctionTable) : Progress :=
  let counts := table.functions.foldl (init := (0, 0, 0, 0, 0)) fun (ns, ip, im, t, d) f =>
    match f.status with
    | .notStarted => (ns + 1, ip, im, t, d)
    | .inProgress => (ns, ip + 1, im, t, d)
    | .implemented => (ns, ip, im + 1, t, d)
    | .tested => (ns, ip, im, t + 1, d)
    | .documented => (ns, ip, im, t, d + 1)
  { total := table.functions.size
    notStarted := counts.1
    inProgress := counts.2.1
    implemented := counts.2.2.1
    tested := counts.2.2.2.1
    documented := counts.2.2.2.2 }

/-- Compute the percentage of functions that are implemented, tested, and documented -/
def Progress.percentComplete (p : Progress) : Float :=
  if p.total = 0 then 100.0
  else (p.implemented.toFloat + p.tested.toFloat + p.documented.toFloat) / p.total.toFloat * 100.0

/-- Find a function by name in the table -/
def FunctionTable.find? (table : FunctionTable) (name : Name) : Option TrackedFunction :=
  table.functions.find? fun f => f.name == name

/-- Update a function's status by name -/
def FunctionTable.updateStatus (table : FunctionTable) (name : Name) (status : Status) : FunctionTable :=
  { table with
    functions := table.functions.map fun f =>
      if f.name == name then { f with status := status } else f }

/-- Get all functions with a specific status -/
def FunctionTable.filterByStatus (table : FunctionTable) (status : Status) : Array TrackedFunction :=
  table.functions.filter fun f => f.status == status

/-- Get all functions that reference a specific function -/
def FunctionTable.getReferencingFunctions (table : FunctionTable) (target : Name) : Array TrackedFunction :=
  table.functions.filter fun f => 
    f.refs.contains target || f.typedRefs.any (fun r => r.target == target)

/-- Get all functions referenced by a specific function -/
def FunctionTable.getReferencedFunctions (table : FunctionTable) (source : Name) : Array Name :=
  match table.find? source with
  | none => #[]
  | some f => f.refs ++ f.typedRefs.map (fun r => r.target)

/-- Add a typed cross-reference to a function -/
def FunctionTable.addTypedReference (table : FunctionTable) (source : Name) (ref : CrossReference) : FunctionTable :=
  { table with
    functions := table.functions.map fun f =>
      if f.name == source then 
        { f with typedRefs := f.typedRefs.push ref }
      else f }

/-- Update a function's Verso link -/
def FunctionTable.updateVersoLink (table : FunctionTable) (name : Name) (link : String) : FunctionTable :=
  { table with
    functions := table.functions.map fun f =>
      if f.name == name then { f with versoLink := some link } else f }

/-- Generate a markdown documentation section for the function table -/
def FunctionTable.toMarkdown (table : FunctionTable) : String := 
  let header := "| Name | Status | File | Lines | Complexity |\n|------|--------|------|-------|------------|\n"
  let rows := table.functions.map fun f =>
    let file := f.file.getD "-"
    let lines := match f.lines with
      | some (s, e) => s!"{s}-{e}"
      | none => "-"
    let complexity := f.complexity.getD "-"
    s!"| {f.name} | {f.status.toSymbol} | {file} | {lines} | {complexity} |"
  header ++ String.intercalate "\n" rows.toList

/-- Integration with hover info - show function status in hover -/
def TrackedFunction.hoverInfo (f : TrackedFunction) : String :=
  s!"{f.name} [{f.status.toSymbol}]" ++
  (match f.docString with
   | some doc => s!"\n{doc}"
   | none => "") ++
  (match f.versoLink with
   | some link => s!"\nDocs: {link}"
   | none => "") ++
  (if f.refs.isEmpty then "" else s!"\nSee also: {f.refs}") ++
  (if f.typedRefs.isEmpty then "" else 
    let refStr := f.typedRefs.toList.map (fun r => s!"{r.refType}({r.target})") |> String.intercalate ", "
    s!"\nReferences: {refStr}")

end FuncTracker