
//============ Spec Dependencies ===============

function intMax (x: int, y: int) : int 
{
  if x < y then y else x
}

predicate LongestIncreasingSubsequence_precond(a: seq<int>)
{
    true
}

predicate LongestIncreasingSubsequence_postcond(a: seq<int>, result: int)
    requires LongestIncreasingSubsequence_precond(a)
{
    var lengths := IncreasingSubseqLengths(a);
    result in lengths && (forall len :: len in lengths ==> len <= result)
}

//=========================================


//=========== Your helpers ================
//=========================================


//=========== Main Task ===================
method  LongestIncreasingSubsequence_postcond (a : Array<Int>) returns (result: Int) 
	requires LongestIncreasingSubsequence_precond (a)
	ensures LongestIncreasingSubsequence_postcond (a, result)
{
	
}
//=========================================