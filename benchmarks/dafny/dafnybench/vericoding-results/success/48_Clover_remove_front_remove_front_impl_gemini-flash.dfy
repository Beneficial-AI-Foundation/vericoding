

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method remove_front(a:array<int>) returns (c:array<int>)
  requires a.Length>0
  ensures  a[1..] == c[..]
// </vc-spec>
// <vc-code>
{
    var n := a.Length;
    if n == 1 {
        return new int[0];
    } else {
        var c_len := n - 1;
        var c := new int[c_len];
        var i := 0;
        while i < c_len 
            invariant 0 <= i <= c_len
            invariant forall k :: 0 <= k < i ==> c[k] == a[k + 1]
        {
            c[i] := a[i + 1];
            i := i + 1;
        }
        return c;
    }
}
// </vc-code>

