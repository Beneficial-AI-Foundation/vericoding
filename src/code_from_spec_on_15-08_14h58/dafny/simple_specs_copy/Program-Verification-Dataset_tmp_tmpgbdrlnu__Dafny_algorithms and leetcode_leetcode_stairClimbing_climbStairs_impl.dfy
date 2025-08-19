//ATOM

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

function climbStairsSeqs(n: nat): set<seq<Steps>>
  decreases n
{
  if n == 0 then {[]}
  else if n == 1 then {[One]}
  else 
    var fromN1 := climbStairsSeqs(n-1);
    var fromN2 := climbStairsSeqs(n-2);
    (set s | s in fromN1 :: [One] + s) + 
    (set s | s in fromN2 :: [Two] + s)
}

lemma climbStairsSeqsCorrect(n: nat)
  ensures allEndAtN(climbStairsSeqs(n), n)
  decreases n
{
  if n == 0 {
    assert sumSteps([]) == 0;
  }
  else if n == 1 {
    assert sumSteps([One]) == 1;
  }
  else {
    climbStairsSeqsCorrect(n-1);
    climbStairsSeqsCorrect(n-2);
    var fromN1 := climbStairsSeqs(n-1);
    var fromN2 := climbStairsSeqs(n-2);
    var result := (set s | s in fromN1 :: [One] + s) + (set s | s in fromN2 :: [Two] + s);
    
    forall seq_steps | seq_steps in result
      ensures sumSteps(seq_steps) == n
    {
      if seq_steps in (set s | s in fromN1 :: [One] + s) {
        var s :| s in fromN1 && seq_steps == [One] + s;
        assert sumSteps(s) == n - 1;
        assert sumSteps(seq_steps) == 1 + sumSteps(s) == n;
      } else {
        var s :| s in fromN2 && seq_steps == [Two] + s;
        assert sumSteps(s) == n - 2;
        assert sumSteps(seq_steps) == 2 + sumSteps(s) == n;
      }
    }
  }
}

method climbStairs(n: nat) returns (count: nat) 
  ensures exists ss: set< seq<Steps> > :: count == |ss| && allEndAtN(ss, n)
{
  var ss := climbStairsSeqs(n);
  climbStairsSeqsCorrect(n);
  count := |ss|;
}