// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): new helper to find index of first non-matching element, replacing dropwhile */
function IndexOfFirstNotMatching(s: seq<int>, val: int): (k: nat)
  decreases |s|
  ensures 0 <= k <= |s|
  ensures forall i :: 0 <= i < k ==> s[i] == val
  ensures k < |s| ==> s[k] != val
{
  if |s| == 0 then 0
  else if s[0] != val then 0
  else 1 + IndexOfFirstNotMatching(s[1..], val)
}

/* helper modified by LLM (iteration 4): replaced non-existent 'dropwhile' with a helper call */
function {:fuel UniqueElementsCount, 2} UniqueElementsCount(s: seq<int>): nat
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  decreases s
{
  if s == [] then 0
  else 1 + UniqueElementsCount( (s[1..])[IndexOfFirstNotMatching(s[1..], s[0])..] )
}

/* helper modified by LLM (iteration 4): replaced non-existent 'dropwhile' with a helper call */
lemma UniqueElementsCount_ensures(s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures UniqueElementsCount(s) <= |s|
  decreases s
{
  if s != [] {
    var rest := (s[1..])[IndexOfFirstNotMatching(s[1..], s[0])..];
    UniqueElementsCount_ensures(rest);
  }
}
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(nums: seq<int>) returns (result: nat)
    requires forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
    ensures result <= |nums|
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): no logical change as error was in helpers */
    result := UniqueElementsCount(nums);
    UniqueElementsCount_ensures(nums);
}
// </vc-code>
