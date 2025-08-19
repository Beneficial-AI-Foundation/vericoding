import FuncTracker.Native2D
import FuncTracker.BasicV2

namespace FuncTracker.Demo2D

open FuncTracker
open FuncTracker.TwoD.Native

/-!
# Demo: Native 2D Table Syntax

This file demonstrates the new native 2D table syntax functionality
in Phase 1 of the FuncTracker 2D implementation.
-/

-- Example 1: Simple table using the transitional simpleTable2d syntax
def basicTable := simpleTable2d "╔══════════════╦═══════════╦═════════════╗
║ Function     ║ Status    ║ File        ║
╠══════════════╬═══════════╬═════════════╣
║ List.map     ║ ✓✓✓       ║ List.lean   ║
║ Array.map    ║ ✓✓        ║ Array.lean  ║
║ Option.map   ║ ✓         ║ -           ║
╚══════════════╩═══════════╩═════════════╝"

-- Test that it works
#eval basicTable.functions.size

-- Check progress computation
#eval basicTable.computeProgress

-- Pretty-print the table
#eval functionTableTo2D basicTable

-- Example 2: More comprehensive table
def comprehensiveTable := simpleTable2d "╔════════════════════╦═══════════╦══════════════╗
║ Function           ║ Status    ║ File         ║
╠════════════════════╬═══════════╬══════════════╣
║ List.map           ║ ✓✓✓       ║ List.lean    ║
║ List.filter        ║ ✓✓        ║ List.lean    ║
║ Array.map          ║ ✓✓        ║ Array.lean   ║
║ Array.filter       ║ ✓         ║ Array.lean   ║
║ Option.map         ║ ✓         ║ -            ║
║ Nat.add            ║ ✗         ║ -            ║
╚════════════════════╩═══════════╩══════════════╝"

-- Show progress statistics
#eval do
  let progress := comprehensiveTable.computeProgress
  IO.println s!"Total functions: {progress.total}"
  IO.println s!"Documented: {progress.documented}"
  IO.println s!"Tested: {progress.tested}"
  IO.println s!"Implemented: {progress.implemented}"
  IO.println s!"In progress: {progress.inProgress}"
  IO.println s!"Not started: {progress.notStarted}"
  IO.println s!"Completion: {progress.percentComplete}%"

-- Example 3: Testing the 2D parsing infrastructure directly
open FuncTracker.TwoD
open FuncTracker.TwoD.SpatialParser

def testTableText := "╔══════════════╦═══════════╦═════════════╗
║ Function     ║ Status    ║ File        ║
╠══════════════╬═══════════╬═════════════╣
║ List.map     ║ ✓✓✓       ║ List.lean   ║
║ Array.map    ║ ✓✓        ║ Array.lean  ║
╚══════════════╩═══════════╩═════════════╝"

-- Parse the table structure
#eval parseTableToFunctionData testTableText

-- Test grid parsing
#eval parseSimpleTable testTableText

-- Show parsing diagnostics
#eval formatParsingDiagnostics testTableText

end FuncTracker.Demo2D