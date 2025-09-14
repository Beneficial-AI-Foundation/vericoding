// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/GW7a

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://www.rise4fun.com/Dafny/JPGct

// Klárið að forrita föllin tvö.

// <vc-helpers>
function new_multiset<T>(): multiset<T> {
    multiset{}
}
// </vc-helpers>

// <vc-spec>
method Partition( m: multiset<int> )
        returns( pre: multiset<int>, p: int, post: multiset<int> )
    requires |m| > 0;
    ensures p in m;
    ensures m == pre+multiset{p}+post;
     ensures forall z | z in pre :: z <= p;
     ensures forall z | z in post :: z >= p;
// </vc-spec>
// <vc-code>
{
    var k := ( |m| / 2 );
    var p_val: int;
    if |m| > 0 {
        p_val := m.Select(k);
    } else {
        // This should not be reached due to requires |m| > 0,
        // but Dafny needs guaranteed initialization.
        p_val := 0;
    }
    p := p_val;

    var less_than_p := new_multiset();
    var greater_than_p := new_multiset();
    var equal_to_p := new_multiset();

    // Iterate through the multiset elements using a loop over the elements for which a count is available.
    // This allows iterating over distinct elements.
    for distinct_x_val_in_m : int | m[distinct_x_val_in_m] > 0
        invariant less_than_p + greater_than_p + equal_to_p <= m
        invariant forall z | z in less_than_p :: z < p
        invariant forall z | z in greater_than_p :: z > p
        invariant forall z | z in equal_to_p :: z == p
        invariant forall z | z in m && !(z in less_than_p) && !(z in greater_than_p) && !(z in equal_to_p) :: true // All existing elements in m are either accounted for or will be processed.
    {
        var count := m[distinct_x_val_in_m];
        if distinct_x_val_in_m < p {
            less_than_p := less_than_p + multiset{distinct_x_val_in_m := count};
        } else if distinct_x_val_in_m > p {
            greater_than_p := greater_than_p + multiset{distinct_x_val_in_m := count};
        } else {
            equal_to_p := equal_to_p + multiset{distinct_x_val_in_m := count};
        }
    }
    
    pre := less_than_p;
    post := greater_than_p + (equal_to_p - multiset{p});

    // Final checks to satisfy postconditions
    assert p in m;
    assert m == less_than_p + multiset{p} + (equal_to_p - multiset{p}) + greater_than_p;
    assert m == pre + multiset{p} + post;
}
// </vc-code>

