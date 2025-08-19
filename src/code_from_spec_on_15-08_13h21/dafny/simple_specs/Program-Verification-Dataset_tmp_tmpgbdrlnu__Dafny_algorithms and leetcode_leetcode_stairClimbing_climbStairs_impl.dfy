datatype Steps = One | Two


//IMPL 

predicate allEndAtN(ss: set<seq<Steps>>, n: nat)
{
  forall s :: s in ss ==> sumSteps(s) == n
}

function sumSteps(s: seq<Steps>): nat
{
  if |s| == 0 then 0
  else (if s[0] == One then 1 else 2) + sumSteps(s[1..])
}

function generateStairSequences(n: nat): set<seq<Steps>>
  decreases n
{
  if n == 0 then {[]}
  else if n == 1 then {[One]}
  else 
    var withOne := set s | s in generateStairSequences(n-1) :: [One] + s;
    var withTwo := set s | s in generateStairSequences(n-2) :: [Two] + s;
    withOne + withTwo
}

lemma StairSequencesCorrect(n: nat)
  ensures allEndAtN(generateStairSequences(n), n)
{
  if n == 0 {
    assert sumSteps([]) == 0;
  } else if n == 1 {
    assert sumSteps([One]) == 1;
  } else {
    StairSequencesCorrect(n-1);
    StairSequencesCorrect(n-2);
    
    var withOne := set s | s in generateStairSequences(n-1) :: [One] + s;
    var withTwo := set s | s in generateStairSequences(n-2) :: [Two] + s;
    
    /* code modified by LLM (iteration 1): Fixed forall statement syntax by changing variable name from 'seq' to 'sequence' and adding proper body */
    forall sequence | sequence in withOne 
      ensures sumSteps(sequence) == n
    {
      var s :| s in generateStairSequences(n-1) && sequence == [One] + s;
      assert sumSteps(sequence) == 1 + sumSteps(s) == 1 + (n-1) == n;
    }
    
    /* code modified by LLM (iteration 1): Fixed forall statement syntax by changing variable name from 'seq' to 'sequence' */
    forall sequence | sequence in withTwo
      ensures sumSteps(sequence) == n  
    {
      var s :| s in generateStairSequences(n-2) && sequence == [Two] + s;
      assert sumSteps(sequence) == 2 + sumSteps(s) == 2 + (n-2) == n;
    }
  }
}

method climbStairs(n: nat) returns (count: nat) 
  ensures exists ss: set< seq<Steps> > :: count == |ss| && allEndAtN(ss, n)
{
  var ss := generateStairSequences(n);
  StairSequencesCorrect(n);
  count := |ss|;
}