import FuncTracker.Native2D
import FuncTracker.PrettyFormat
import FuncTracker.BasicV2

namespace FuncTracker.Demo2DAdvanced

open FuncTracker
open FuncTracker.TwoD.Native
open FuncTracker.TwoD.PrettyFormat

/-!
# Demo: Advanced 2D Table Formatting (Phase 2)

This file demonstrates the advanced formatting capabilities introduced in Phase 2,
including dynamic styling, multiple export formats, and automatic beautification.
-/

-- Example table for testing advanced features
def sampleTable := simpleTable2d "╔════════════════════╦═══════════╦══════════════╗
║ Function           ║ Status    ║ File         ║
╠════════════════════╬═══════════╬══════════════╣
║ List.map           ║ ✓✓✓       ║ List.lean    ║
║ List.filter        ║ ✓✓        ║ List.lean    ║
║ Array.map          ║ ✓✓        ║ Array.lean   ║
║ Array.filter       ║ ✓         ║ Array.lean   ║
║ Option.map         ║ ✓         ║ -            ║
║ Nat.add            ║ ✗         ║ -            ║
║ String.append      ║ ⋯         ║ String.lean  ║
╚════════════════════╩═══════════╩══════════════╝"

-- Demo 1: Different styling options
#eval IO.println "=== ELEGANT STYLE ==="
#eval IO.println (formatFunctionTable sampleTable Styles.elegant)

#eval IO.println "\n=== MINIMAL STYLE ==="
#eval IO.println (formatFunctionTable sampleTable Styles.minimal)

#eval IO.println "\n=== COMPACT STYLE ==="
#eval IO.println (formatFunctionTable sampleTable Styles.compact)

#eval IO.println "\n=== ROUNDED STYLE ==="
#eval IO.println (formatFunctionTable sampleTable Styles.rounded)

-- Demo 2: Automatic content analysis and formatting
#eval IO.println "\n=== AUTO-ANALYZED FORMAT ==="
#eval IO.println (AdvancedFormat.analyzeAndFormat sampleTable)

-- Demo 3: Context-specific formatting
#eval IO.println "\n=== PRESENTATION FORMAT ==="
#eval IO.println (AdvancedFormat.formatForContext sampleTable "presentation")

#eval IO.println "\n=== DEVELOPMENT FORMAT ==="
#eval IO.println (AdvancedFormat.formatForContext sampleTable "development")

-- Demo 4: Export to different formats
#eval do
  let exports := TableExport.exportAll sampleTable
  
  IO.println "\n=== MARKDOWN EXPORT ==="
  IO.println exports.markdown
  
  IO.println "\n=== HTML EXPORT ==="
  IO.println exports.html
  
  IO.println "\n=== LATEX EXPORT ==="
  IO.println exports.latex
  
  IO.println "\n=== CSV EXPORT ==="
  IO.println exports.csv

-- Demo 5: Custom formatting with specific column configurations
def customFormat : TableFormat := {
  borderStyle := .heavy,
  columnFormats := #[
    { minWidth := 25, alignment := .left, padding := (2, 1) },    -- Function names, left-aligned with extra space
    { minWidth := 12, alignment := .center, padding := (1, 1) },  -- Status, centered
    { minWidth := 18, alignment := .right, padding := (1, 2) }    -- File, right-aligned
  ],
  includeHeaderSeparator := true
}

#eval IO.println "\n=== CUSTOM FORMAT ==="
#eval IO.println (formatFunctionTable sampleTable customFormat)

-- Demo 6: Table with many functions to test scalability
def largeTable := simpleTable2d "╔══════════════════════════╦═══════════╦══════════════╗
║ Function                 ║ Status    ║ File         ║
╠══════════════════════════╬═══════════╬══════════════╣
║ List.map                 ║ ✓✓✓       ║ List.lean    ║
║ List.filter              ║ ✓✓        ║ List.lean    ║
║ List.foldl               ║ ✓✓✓       ║ List.lean    ║
║ List.foldr               ║ ✓✓        ║ List.lean    ║
║ Array.map                ║ ✓✓        ║ Array.lean   ║
║ Array.filter             ║ ✓         ║ Array.lean   ║
║ Array.foldl              ║ ✓✓        ║ Array.lean   ║
║ Option.map               ║ ✓         ║ -            ║
║ Option.bind              ║ ✓✓        ║ -            ║
║ Nat.add                  ║ ✗         ║ -            ║
║ Nat.mul                  ║ ✗         ║ -            ║
║ String.append            ║ ⋯         ║ String.lean  ║
║ String.length            ║ ✓✓✓       ║ String.lean  ║
║ IO.println               ║ ✓✓✓       ║ -            ║
║ HashMap.insert           ║ ⋯         ║ HashMap.lean ║
╚══════════════════════════╩═══════════╩══════════════╝"

#eval IO.println "\n=== LARGE TABLE AUTO-FORMAT ==="
#eval IO.println (AdvancedFormat.analyzeAndFormat largeTable)

-- Demo 7: Progress analysis on the large table
#eval do
  let progress := largeTable.computeProgress
  IO.println s!"\n=== PROGRESS ANALYSIS ==="
  IO.println s!"Total functions: {progress.total}"
  IO.println s!"Documented (✓✓✓): {progress.documented}"
  IO.println s!"Tested (✓✓): {progress.tested}"
  IO.println s!"Implemented (✓): {progress.implemented}"
  IO.println s!"In progress (⋯): {progress.inProgress}"
  IO.println s!"Not started (✗): {progress.notStarted}"
  IO.println s!"Overall completion: {progress.percentComplete:.1f}%"

-- Demo 8: Side-by-side format comparison
def compareFormats (table : FunctionTable) : IO Unit := do
  IO.println "╔════════════════════════════════════════════════════════════════════════════════╗"
  IO.println "║                            FORMAT COMPARISON                                  ║"
  IO.println "╚════════════════════════════════════════════════════════════════════════════════╝"
  
  IO.println "\n🎨 ELEGANT (for presentations):"
  IO.println (formatFunctionTable table Styles.elegant)
  
  IO.println "\n⚡ MINIMAL (for development):"
  IO.println (formatFunctionTable table Styles.minimal)
  
  IO.println "\n📦 COMPACT (space-efficient):"
  IO.println (formatFunctionTable table Styles.compact)
  
  IO.println "\n🔄 ROUNDED (modern look):"
  IO.println (formatFunctionTable table Styles.rounded)

#eval compareFormats sampleTable

-- Demo 9: Export format showcase
def showcaseExports (table : FunctionTable) : IO Unit := do
  let exports := TableExport.exportAll table
  
  IO.println "\n📄 MARKDOWN (for documentation):"
  IO.println exports.markdown
  
  IO.println "\n🌐 HTML (for web pages):"
  IO.println exports.html
  
  IO.println "\n📚 LATEX (for academic papers):"
  IO.println exports.latex
  
  IO.println "\n📊 CSV (for spreadsheets):"
  IO.println exports.csv

#eval showcaseExports sampleTable

-- Demo 10: Automatic formatting based on table characteristics
def smartFormat (table : FunctionTable) : IO Unit := do
  let numFunctions := table.functions.size
  let hasComplexNames := table.functions.any (fun f => f.name.toString.length > 15)
  let hasFiles := table.functions.any (fun f => f.file.isSome)
  
  IO.println s!"\n🧠 SMART FORMATTING ANALYSIS:"
  IO.println s!"• Functions: {numFunctions}"
  IO.println s!"• Complex names: {hasComplexNames}"
  IO.println s!"• Has file info: {hasFiles}"
  
  let recommendedStyle := 
    if numFunctions > 10 then "minimal"
    else if hasComplexNames then "elegant"
    else "rounded"
  
  IO.println s!"• Recommended style: {recommendedStyle}"
  IO.println "\nFormatted result:"
  IO.println (AdvancedFormat.formatForContext table recommendedStyle)

#eval smartFormat largeTable

end FuncTracker.Demo2DAdvanced