

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Mid( p: int, q: int) returns ( m: int )
    // | ... | ??? | ... |
    //        p m   q
    requires p <= q;
    ensures p<= m <= q;
    ensures m-p <= q-m;
    ensures 0 <= (q-m)-(m-p) <= 1;
// </vc-spec>
// <vc-code>
{ m := p + ((q - p) / 2); }
// </vc-code>

