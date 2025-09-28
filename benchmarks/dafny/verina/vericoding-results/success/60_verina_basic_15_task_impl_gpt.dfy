// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): safe check for consecutive pair at index i */
function IsConsecutivePair(a: seq<int>, i: int): bool
    requires 0 <= i
    requires i + 1 < |a|
{
    a[i] + 1 == a[i + 1]
}

/* helper modified by LLM (iteration 2): exists-based check for any consecutive pair in the sequence */
function HasConsecutive(a: seq<int>): bool
{
    exists i :: 0 <= i && i + 1 < |a| && a[i] + 1 == a[i + 1]
}
// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(a: seq<int>) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |a| - 1 && a[i] + 1 == a[i + 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute result via pure helper that encapsulates the specification */
  result := HasConsecutive(a);
}
// </vc-code>
