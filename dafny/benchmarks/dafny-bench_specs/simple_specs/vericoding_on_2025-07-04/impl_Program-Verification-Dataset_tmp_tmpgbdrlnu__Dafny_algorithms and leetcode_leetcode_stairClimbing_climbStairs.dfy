//ATOM

datatype Steps = One | Two

//IMPL climbStairs
/* code modified by LLM (iteration 1): Added helper predicate and implementation */

// Helper predicate to check if all sequences in a set sum to n
predicate allEndAtN(ss: set<seq<Steps>>, n: nat)
{
  forall s :: s in ss ==> sumSteps(s) == n
}

// Helper function to sum the steps in a sequence
function sumSteps(s: seq<Steps>): nat
{
  if |s| == 0 then 0
  else (if s[0] == One then 1 else 2) + sumSteps(s[1..])
}

// Helper function to generate all valid step sequences that sum to n
function generateStepSequences(n: nat): set<seq<Steps>>
  decreases n
{
  if n == 0 then {[]}
  else if n == 1 then {[One]}
  else 
    var withOne := set s | s in generateStepSequences(n-1) :: [One] + s;
    var withTwo := set s | s in generateStepSequences(n-2) :: [Two] + s;
    withOne + withTwo
}

// Lemma to prove that generateStepSequences produces valid sequences
lemma generateStepSequencesCorrect(n: nat)
  ensures var ss := generateStepSequences(n);
          allEndAtN(ss, n)
  decreases n
{
  if n <= 1 {
    // Base cases are trivial
  } else {
    generateStepSequencesCorrect(n-1);
    generateStepSequencesCorrect(n-2);
    
    var ss := generateStepSequences(n);
    var ss1 := generateStepSequences(n-1);
    var ss2 := generateStepSequences(n-2);
    
    forall s | s in ss
      ensures sumSteps(s) == n
    {
      if s in set s | s in ss1 :: [One] + s {
        var s' :| s' in ss1 && s == [One] + s';
        assert sumSteps(s') == n-1;
        assert sumSteps(s) == 1 + sumSteps(s') == n;
      } else {
        assert s in set s | s in ss2 :: [Two] + s;
        var s' :| s' in ss2 && s == [Two] + s';
        assert sumSteps(s') == n-2;
        assert sumSteps(s) == 2 + sumSteps(s') == n;
      }
    }
  }
}

method climbStairs(n: nat) returns (count: nat) 
  ensures exists ss: set< seq<Steps> > :: count == |ss| && allEndAtN(ss, n)
{
  /* code modified by LLM (iteration 1): Implemented method body using helper functions */
  var ss := generateStepSequences(n);
  generateStepSequencesCorrect(n);
  count := |ss|;
}