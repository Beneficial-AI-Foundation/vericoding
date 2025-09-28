// <vc-preamble>
// Helper function to count the number of true values in a boolean sequence
function CountTrue(condition: seq<bool>): nat
{
    if |condition| == 0 then 0
    else (if condition[0] then 1 else 0) + CountTrue(condition[1..])
}

// Helper function to get the i-th true position in the condition array
function GetIthTruePosition(condition: seq<bool>, i: nat): nat
    requires i < CountTrue(condition)
    decreases |condition|
{
    if |condition| == 0 then 0
    else if condition[0] then
        if i == 0 then 0
        else 1 + GetIthTruePosition(condition[1..], i - 1)
    else 1 + GetIthTruePosition(condition[1..], i)
}

// Helper predicate to check if a position is the k-th true position
predicate IsKthTruePosition(condition: seq<bool>, pos: nat, k: nat)
    requires pos < |condition|
    requires k < CountTrue(condition)
{
    GetIthTruePosition(condition, k) == pos
}

/**
 * Extract elements from an array where the corresponding condition is true.
 * Returns a new sequence containing only the elements at positions where 
 * condition is true, preserving their original order.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [changed to suffix-recursive for iterative proof] */
function {:auto_generated} RecursiveExtract(condition: seq<bool>, arr: seq<int>): seq<int>
    requires |condition| == |arr|
    decreases |arr|
{
    if |arr| == 0 then []
    else
        var prev := RecursiveExtract(condition[..|arr|-1], arr[..|arr|-1]);
        if condition[|arr|-1] then prev + [arr[|arr|-1]]
        else prev
}

/* helper modified by LLM (iteration 5): [new lemma to reason about CountTrue with append] */
lemma CountTrueAppend(s: seq<bool>, b: bool)
    ensures CountTrue(s + [b]) == CountTrue(s) + (if b then 1 else 0)
    decreases |s|
{
    if |s| > 0 {
        CountTrueAppend(s[1..], b);
    }
}

/* helper modified by LLM (iteration 5): [added ensures for position correctness] */
lemma GetIthTruePositionProps(condition: seq<bool>, i: nat)
    requires i < CountTrue(condition)
    ensures GetIthTruePosition(condition, i) < |condition|
    ensures condition[GetIthTruePosition(condition, i)]
    decreases |condition|
{
    if |condition| > 0 {
        if condition[0] {
            if i > 0 {
                GetIthTruePositionProps(condition[1..], i - 1);
            }
        } else {
            GetIthTruePositionProps(condition[1..], i);
        }
    }
}

/* helper modified by LLM (iteration 5): [new lemma for GetIthTruePosition with append] */
lemma GetIthPosAppend(s: seq<bool>, b: bool, k: nat)
    requires k < CountTrue(s)
    ensures GetIthTruePosition(s + [b], k) == GetIthTruePosition(s, k)
    decreases |s|
{
    CountTrueAppend(s, b);
    if |s| > 0 {
      if s[0] {
        if k > 0 { GetIthPosAppend(s[1..], b, k-1); }
      } else {
        GetIthPosAppend(s[1..], b, k);
      }
    }
}

/* helper modified by LLM (iteration 5): [new lemma for GetIthTruePosition of last true element] */
lemma GetIthPosAppendTrueLast(s: seq<bool>)
    ensures GetIthTruePosition(s + [true], CountTrue(s)) == |s|
    decreases |s|
{
    CountTrueAppend(s, true);
    if |s| > 0 {
        if s[0] {
            GetIthPosAppendTrueLast(s[1..]);
        } else {
            GetIthPosAppendTrueLast(s[1..]);
        }
    }
}

/* helper modified by LLM (iteration 5): [fixed postcondition and provided full proof body] */
lemma {:auto_generated} LemmaRecursiveExtractProperties(condition: seq<bool>, arr: seq<int>)
    requires |condition| == |arr|
    ensures |RecursiveExtract(condition, arr)| == CountTrue(condition)
    ensures forall k :: 0 <= k < |RecursiveExtract(condition, arr)| ==>
        var pos := GetIthTruePosition(condition, k);
        pos < |arr| &&
        condition[pos] &&
        RecursiveExtract(condition, arr)[k] == arr[pos]
    decreases |arr|
{
    if |arr| > 0 {
        var cond_prior := condition[..|arr|-1];
        var arr_prior := arr[..|arr|-1];
        var last_cond := condition[|arr|-1];

        LemmaRecursiveExtractProperties(cond_prior, arr_prior);

        CountTrueAppend(cond_prior, last_cond);
        var R := RecursiveExtract(condition, arr);
        assert |R| == CountTrue(condition);

        forall k | 0 <= k < |R|
            ensures var pos := GetIthTruePosition(condition, k); pos < |arr| && condition[pos] && R[k] == arr[pos]
        {
            GetIthTruePositionProps(condition, k);
            if last_cond {
                if k < CountTrue(cond_prior) {
                    GetIthPosAppend(cond_prior, true, k);
                } else {
                    GetIthPosAppendTrueLast(cond_prior);
                }
            } else {
                GetIthPosAppend(cond_prior, false, k);
            }
        }
    }
}

// </vc-helpers>

// <vc-spec>
method Extract(condition: seq<bool>, arr: seq<int>) returns (result: seq<int>)
    requires |condition| == |arr|
    ensures |result| == CountTrue(condition)
    // Each element in result comes from arr at a position where condition is true
    ensures forall k :: 0 <= k < |result| ==> 
        exists i :: 0 <= i < |arr| && condition[i] && result[k] == arr[i]
    // The order is preserved: elements appear in the same relative order as in arr
    ensures forall k1, k2 :: 0 <= k1 < k2 < |result| ==> 
        exists i1, i2 :: (0 <= i1 < i2 < |arr| && 
        condition[i1] && condition[i2] && 
        result[k1] == arr[i1] && result[k2] == arr[i2])
    // Every true position in condition contributes exactly one element to the result
    ensures forall i :: 0 <= i < |arr| && condition[i] ==> 
        exists k :: 0 <= k < |result| && result[k] == arr[i]
    // More precise: the k-th element of result corresponds to the k-th true position in condition
    ensures forall k :: 0 <= k < |result| ==> 
        var pos := GetIthTruePosition(condition, k);
        pos < |arr| && condition[pos] && result[k] == arr[pos]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): [using suffix-recursive helper to prove loop invariant and calling lemma for postconditions] */
  result := [];
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant result == RecursiveExtract(condition[..i], arr[..i])
  {
    if condition[i] {
        result := result + [arr[i]];
    }
    i := i + 1;
  }
  LemmaRecursiveExtractProperties(condition, arr);
}

// </vc-code>
