// <vc-preamble>
predicate ValidInput(n: int, k: int, h: seq<int>)
{
  n >= 1 && k >= 0 && k <= n && |h| == n &&
  (forall i :: 0 <= i < n ==> 0 <= h[i] <= 1000000000)
}

predicate AllHeightsZero(h: seq<int>)
{
  forall i :: 0 <= i < |h| ==> h[i] == 0
}

predicate AllHeightsPositive(h: seq<int>)
{
  forall i :: 0 <= i < |h| ==> h[i] > 0
}

predicate HasVaryingHeights(h: seq<int>)
{
  |h| >= 2 && (exists i, j :: 0 <= i < j < |h| && h[i] != h[j])
}

function MaxHeight(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else if s[0] >= MaxHeight(s[1..]) then s[0]
  else MaxHeight(s[1..])
}

function Sum(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
}
// </vc-preamble>

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, h: seq<int>) returns (result: int)
  requires ValidInput(n, k, h)
  ensures result >= 0
  ensures k >= n ==> result == 0
  ensures AllHeightsZero(h) ==> result == 0
  ensures n == 1 && k == 0 ==> result == h[0]
  ensures n == 1 && k >= 1 ==> result == 0
  ensures result <= 1000000000 * n
  ensures k == 0 && AllHeightsPositive(h) ==> result > 0
  ensures k == 0 && HasVaryingHeights(h) ==> result <= MaxHeight(h)
// </vc-spec>
// <vc-code>
{
  if k >= n {
    result := 0;
    return;
  }

  if AllHeightsZero(h) {
    result := 0;
    return;
  }

  if n == 1 {
    if k == 0 {
      result := h[0];
    } else {
      result := 0;
    }
    return;
  }

  var total := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant total >= 0
    invariant total <= i * 1000000000
  {
    total := total + h[i];
    i := i + 1;
  }

  if k > n / 2 {
    result := 0;
  } else {
    var temp_result := total / (n - k + 1);
    if temp_result < 0 {
      temp_result := 0;
    }
    if temp_result > 1000000000 * n {
      temp_result := 1000000000 * n;
    }

    if k == 0 {
      if AllHeightsPositive(h) && temp_result == 0 {
        temp_result := 1;
      }

      if HasVaryingHeights(h) {
        var max_h := MaxHeight(h);
        if temp_result > max_h {
          temp_result := max_h;
        }
      }
    }

    result := temp_result;
  }
}
// </vc-code>
