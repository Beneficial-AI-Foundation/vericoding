// <vc-preamble>
/* Helper: Product of a sequence of integers */
function ListProduct(nums: seq<int>): int
    decreases |nums|
{
    if |nums| == 0 then 1 else nums[0] * ListProduct(nums[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): unfold property of ListProduct on non-empty sequences */
lemma ListProduct_Unfold_NonEmpty(s: seq<int>)
  requires |s| > 0
  ensures ListProduct(s) == s[0] * ListProduct(s[1..])
{
  calc {
    ListProduct(s);
    == { }
    (if |s| == 0 then 1 else s[0] * ListProduct(s[1..]));
    == { assert |s| > 0; }
    s[0] * ListProduct(s[1..]);
  }
}

/* helper modified by LLM (iteration 4): product over snoc (append single element) */
lemma ListProduct_Snoc(s: seq<int>, x: int)
  ensures ListProduct(s + [x]) == ListProduct(s) * x
  decreases |s|
{
  if |s| == 0 {
    assert s == [];
    calc {
      ListProduct(s + [x]);
      == { assert s + [x] == [x]; }
      ListProduct([x]);
      == { }
      [x][0] * ListProduct([x][1..]);
      == { }
      ListProduct([]) * x;
      == { assert s == []; }
      ListProduct(s) * x;
    }
  } else {
    ListProduct_Snoc(s[1..], x);
    calc {
      ListProduct(s + [x]);
      == { }
      (s + [x])[0] * ListProduct((s + [x])[1..]);
      == { assert (s + [x])[0] == s[0]; assert (s + [x])[1..] == s[1..] + [x]; }
      s[0] * ListProduct(s[1..] + [x]);
      == { }
      s[0] * (ListProduct(s[1..]) * x);
      == { }
      (s[0] * ListProduct(s[1..])) * x;
      == { ListProduct_Unfold_NonEmpty(s); }
      ListProduct(s) * x;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method ProductExceptSelf(nums: array<int>) returns (result: array<int>)
    ensures
        result.Length == nums.Length
    ensures
        forall i :: 0 <= i < nums.Length ==> 
            result[i] == ListProduct(nums[..i]) * ListProduct(nums[i+1..])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): two-pass prefix/suffix product without assumptions */
  var n := nums.Length;
  result := new int[n];

  var i := 0;
  var pref := 1;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant pref == ListProduct(nums[..i])
    invariant forall j :: 0 <= j < i ==> result[j] == ListProduct(nums[..j])
    decreases n - i
  {
    result[i] := pref;
    assert nums[..i+1] == nums[..i] + [nums[i]];
    ListProduct_Snoc(nums[..i], nums[i]);
    pref := pref * nums[i];
    i := i + 1;
  }

  assert forall j :: 0 <= j < n ==> result[j] == ListProduct(nums[..j]);

  i := n - 1;
  var suf := 1;
  while i >= 0
    invariant -1 <= i < n
    invariant result.Length == n
    invariant suf == ListProduct(nums[i+1..])
    invariant forall j :: 0 <= j <= i ==> result[j] == ListProduct(nums[..j])
    invariant forall j :: i < j < n ==> result[j] == ListProduct(nums[..j]) * ListProduct(nums[j+1..])
    decreases i + 1
  {
    result[i] := result[i] * suf;

    assert |nums[i..]| > 0;
    ListProduct_Unfold_NonEmpty(nums[i..]);
    suf := nums[i] * suf;

    i := i - 1;
  }
}
// </vc-code>
