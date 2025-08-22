// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This test ensures that the trigger  collector (the routine that picks trigger
// candidates) does not  actually consider all subsets of terms;  if it did, the
// following would take horribly long

//IMPL SPEC
method M() {
}