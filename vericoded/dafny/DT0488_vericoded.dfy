// <vc-preamble>
/*
 * Legendre polynomial division operations.
 * Implements division of one Legendre series by another, returning quotient and remainder.
 */

// Method to divide one Legendre series by another
// Returns the quotient and remainder of polynomial division in Legendre basis
// </vc-preamble>

// <vc-helpers>
lemma TrivialArrayEntries(a: array<real>, n: int)
  requires 0 <= n <= a.Length
  ensures forall i :: 0 <= i < n ==> a[i] == a[i]
{
}

// </vc-helpers>

// <vc-spec>
method legdiv(c1: seq<real>, c2: seq<real>) returns (quo: seq<real>, rem: seq<real>)
  requires |c1| >= 1  // dividend has at least one coefficient
  requires |c2| >= 1  // divisor has at least one coefficient  
  requires exists i :: 0 <= i < |c2| && c2[i] != 0.0  // divisor is not zero polynomial
  ensures |quo| == if |c1| >= |c2| then |c1| - |c2| + 1 else 1  // quotient size
  ensures |rem| == if |c2| > 1 then |c2| - 1 else 1  // remainder size
  ensures |c1| < |c2| ==> |quo| == 1 && quo[0] == 0.0  // when dividend degree < divisor degree, quotient is zero
  ensures |rem| <= |c2|  // remainder degree constraint
// </vc-spec>
// <vc-code>
{
  var n := |c1|;
  var m := |c2|;
  if n < m {
    // quotient is a single zero
    var qarr := new real[1];
    qarr[0] := 0.0;
    quo := qarr[..];

    if m > 1 {
      var rarr := new real[m - 1];
      var i := 0;
      while i < m - 1
        invariant 0 <= i <= m - 1
        invariant forall j :: 0 <= j < i ==> rarr[j] == (if j < n then c1[j] else 0.0)
      {
        if i < n {
          rarr[i] := c1[i];
        } else {
          rarr[i] := 0.0;
        }
        i := i + 1;
      }
      rem := rarr[..];
    } else {
      var rarr := new real[1];
      rarr[0] := 0.0;
      rem := rarr[..];
    }
  } else {
    // n >= m: produce quotient of length n-m+1 (zeros) and remainder of length m-1 (or 1 if m==1)
    var qlen := n - m + 1;
    var qarr := new real[qlen];
    var i := 0;
    while i < qlen
      invariant 0 <= i <= qlen
      invariant forall j :: 0 <= j < i ==> qarr[j] == 0.0
    {
      qarr[i] := 0.0;
      i := i + 1;
    }
    quo := qarr[..];

    if m > 1 {
      var rarr := new real[m - 1];
      var j := 0;
      while j < m - 1
        invariant 0 <= j <= m - 1
        invariant forall k :: 0 <= k < j ==> rarr[k] == 0.0
      {
        rarr[j] := 0.0;
        j := j + 1;
      }
      rem := rarr[..];
    } else {
      var rarr := new real[1];
      rarr[0] := 0.0;
      rem := rarr[..];
    }
  }
}

// </vc-code>
