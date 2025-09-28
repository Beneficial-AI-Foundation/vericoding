// <vc-preamble>
// Method to subtract one Laguerre series from another
// Input sequences can have different lengths; shorter sequences are implicitly padded with zeros
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int {
    if a >= b then a else b
  }

  /* helper modified by LLM (iteration 3): added SafeGet function for safe sequence access */
  function SafeGet(s: seq<real>, i: int): real {
      if i >= 0 && i < |s| then s[i] else 0.0
  }
// </vc-helpers>

// <vc-spec>
method Lagsub(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
    ensures |result| == if |c1| >= |c2| then |c1| else |c2|  // Result length is max of input lengths
    // Component-wise subtraction with implicit zero-padding: result[i] = (c1[i] or 0) - (c2[i] or 0)
    ensures forall i :: 0 <= i < |result| ==> 
        result[i] == (if i < |c1| then c1[i] else 0.0) - (if i < |c2| then c2[i] else 0.0)
    // The difference of two Laguerre series is a Laguerre series
    // (this is a mathematical property of Laguerre polynomials - subtraction preserves the basis)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): replaced direct sequence access with SafeGet to avoid compilation error */
  var len := max(|c1|, |c2|);
  result := seq(len, i => SafeGet(c1, i) - SafeGet(c2, i));
}
// </vc-code>
