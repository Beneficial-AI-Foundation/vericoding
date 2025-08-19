import Lean
import FuncTracker.BasicV2

namespace FuncTracker

open Lean

/-- Check if one string contains another as a substring -/
def hasSubstring (haystack needle : String) : Bool :=
  needle.isEmpty || (haystack.splitOn needle).length > 1

/-- Verso cross-reference database entry -/
structure VersoReference where
  /-- The identifier being referenced -/
  identifier : String
  /-- The URL where this identifier is documented -/
  url : String
  /-- The title or display name for this reference -/
  title : Option String := none
  /-- The documentation domain this reference belongs to -/
  domain : Option String := none
  /-- Version or revision of the documentation -/
  version : Option String := none
  deriving Repr, BEq, DecidableEq

instance : Inhabited VersoReference where
  default := { identifier := "", url := "" }

/-- Verso cross-reference database -/
structure VersoDatabase where
  /-- Array of all cross-references in the database -/
  references : Array VersoReference
  /-- Base URL for the documentation site -/
  baseUrl : String
  /-- Timestamp when this database was last updated -/
  lastUpdated : Option String := none
  deriving Repr, BEq, DecidableEq

/-- Result of looking up a reference in the Verso database -/
inductive LookupResult where
  | found (ref : VersoReference)
  | notFound
  | multiple (refs : Array VersoReference)
  deriving Repr

/-- Look up a function name in the Verso database -/
def VersoDatabase.lookup (db : VersoDatabase) (identifier : String) : LookupResult :=
  let foundMatches := db.references.filter (fun r => r.identifier == identifier)
  if foundMatches.size == 0 then
    .notFound
  else if foundMatches.size == 1 then
    .found foundMatches[0]!
  else
    .multiple foundMatches

/-- Look up by fuzzy matching (contains substring) -/
def VersoDatabase.fuzzyLookup (db : VersoDatabase) (identifier : String) : Array VersoReference :=
  db.references.filter (fun r => hasSubstring r.identifier identifier)

/-- Update a function table with Verso links from a database -/
def FunctionTable.linkWithVerso (table : FunctionTable) (db : VersoDatabase) : FunctionTable :=
  { table with
    functions := table.functions.map fun f =>
      match db.lookup f.name.toString with
      | .found ref => { f with versoLink := some ref.url, docString := ref.title }
      | _ => f }

/-- Generate Verso cross-reference database from JSON-like structure -/
def parseVersoDatabase (baseUrl : String) (entries : Array (String × String × Option String)) : VersoDatabase :=
  let references := entries.map fun (id, url, title) =>
    { identifier := id, url := url, title := title, domain := some baseUrl }
  { references := references, baseUrl := baseUrl }

/-- Check if a Verso link is valid (basic URL validation) -/
def isValidVersoLink (link : String) : Bool :=
  link.startsWith "http://" || link.startsWith "https://" || link.startsWith "/"

/-- Extract domain from a URL -/
def extractDomain (url : String) : String :=
  if url.startsWith "http://" then
    let rest := url.drop 7
    match rest.splitOn "/" with
    | [] => ""
    | domain :: _ => domain
  else if url.startsWith "https://" then
    let rest := url.drop 8
    match rest.splitOn "/" with
    | [] => ""
    | domain :: _ => domain
  else
    "local"

/-- Generate a cross-reference cache file for InterSphinx-style linking -/
def VersoDatabase.toCacheFormat (db : VersoDatabase) : String :=
  let entries := db.references.map fun ref =>
    s!"  \"{ref.identifier}\": \{\"url\": \"{ref.url}\", \"title\": \"{ref.title.getD ""}\"}"
  "{\n" ++ String.intercalate ",\n" entries.toList ++ "\n}"

/-- Parse a simple CSV-like format for Verso references -/
def parseVersoCSV (csvContent : String) (baseUrl : String) : VersoDatabase :=
  let lines := csvContent.splitOn "\n" |>.filter (fun l => !l.isEmpty && !l.startsWith "#")
  let references := lines.map fun line =>
    let parts := line.splitOn ","
    match parts with
    | [id, url] => { identifier := id.trim, url := url.trim, domain := some baseUrl }
    | [id, url, title] => { identifier := id.trim, url := url.trim, title := some title.trim, domain := some baseUrl }
    | _ => { identifier := line, url := baseUrl ++ "/" ++ line, domain := some baseUrl }
  { references := references.toArray, baseUrl := baseUrl }

/-- Validate cross-references in a function table against a Verso database -/
def validateCrossReferences (table : FunctionTable) (db : VersoDatabase) : Array (Name × String) :=
  table.functions.foldl (init := #[]) fun acc f =>
    f.refs.foldl (init := acc) fun acc2 refName =>
      match db.lookup refName.toString with
      | .notFound => acc2.push (f.name, s!"Reference {refName} not found in Verso database")
      | _ => acc2

/-- Update function table with automatic cross-reference discovery -/
def FunctionTable.discoverCrossReferences (table : FunctionTable) (db : VersoDatabase) : FunctionTable :=
  { table with
    functions := table.functions.map fun f =>
      -- Look for potential references in the function's documentation
      match f.docString with
      | none => f
      | some doc =>
        -- Simple heuristic: look for function names mentioned in the doc
        let potentialRefs := db.references.filter fun ref =>
          ref.identifier.length > 0 && hasSubstring doc ref.identifier && ref.identifier != f.name.toString
        let newRefs := potentialRefs.map fun ref =>
          { target := stringToName ref.identifier, refType := .documents : CrossReference }
        { f with typedRefs := f.typedRefs ++ newRefs } }

/-- Generate Verso-compatible link syntax for embedding in documentation -/
def generateVersoLink (ref : VersoReference) : String :=
  match ref.title with
  | some title => s!"[{title}]({ref.url})"
  | none => s!"[{ref.identifier}]({ref.url})"

/-- Create bidirectional cross-references between functions -/
def FunctionTable.createBidirectionalRefs (table : FunctionTable) : FunctionTable :=
  let bidirectionalRefs := table.functions.foldl (init := #[]) fun acc f =>
    f.typedRefs.foldl (init := acc) fun acc2 ref =>
      match ref.refType with
      | .implements => acc2.push (ref.target, { target := f.name, refType := .implementedBy })
      | .tests => acc2.push (ref.target, { target := f.name, refType := .implementedBy })  -- tested by
      | .documents => acc2.push (ref.target, { target := f.name, refType := .implementedBy })  -- documented by
      | _ => acc2

  -- Apply the bidirectional references
  bidirectionalRefs.foldl (init := table) fun acc (targetName, ref) =>
    acc.addTypedReference targetName ref

end FuncTracker