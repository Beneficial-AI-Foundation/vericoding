Two empires A and B have capitals at coordinates X and Y respectively.
Empire A wants to control cities at coordinates x₁, x₂, ..., xₙ, and 
Empire B wants to control cities at coordinates y₁, y₂, ..., yₘ.
They reach agreement if there exists integer Z such that X < Z ≤ Y,
all xᵢ < Z, and all yᵢ ≥ Z. Otherwise war breaks out.

predicate ValidInput(n: int, m: int, x: int, y: int, xx: seq<int>, yy: seq<int>)
{
    |xx| == n && |yy| == m && n >= 1 && m >= 1 && x < y
}

predicate AgreementPossible(n: int, m: int, x: int, y: int, xx: seq<int>, yy: seq<int>)
    requires ValidInput(n, m, x, y, xx, yy)
{
    var combined_x := xx + [x];
    var combined_y := yy + [y];
    (exists max_val :: max_val in combined_x && 
                     (forall v :: v in combined_x ==> v <= max_val) &&
     exists min_val :: min_val in combined_y && 
                     (forall v :: v in combined_y ==> v >= min_val) &&
                     max_val < min_val)
}

method solve(n: int, m: int, x: int, y: int, xx: seq<int>, yy: seq<int>) returns (result: string)
    requires ValidInput(n, m, x, y, xx, yy)
    ensures result == "No War" || result == "War"
    ensures result == "No War" <==> AgreementPossible(n, m, x, y, xx, yy)
{
    var max_x := x;
    var i := 0;
    while i < |xx|
        invariant 0 <= i <= |xx|
        invariant forall k :: 0 <= k < i ==> xx[k] <= max_x
        invariant max_x >= x
        invariant max_x in xx[0..i] + [x]
    {
        if xx[i] > max_x {
            max_x := xx[i];
        }
        i := i + 1;
    }

    var min_y := y;
    var j := 0;
    while j < |yy|
        invariant 0 <= j <= |yy|
        invariant forall k :: 0 <= k < j ==> yy[k] >= min_y
        invariant min_y <= y
        invariant min_y in yy[0..j] + [y]
    {
        if yy[j] < min_y {
            min_y := yy[j];
        }
        j := j + 1;
    }

    var combined_x := xx + [x];
    var combined_y := yy + [y];

    assert max_x in combined_x;
    assert forall v :: v in combined_x ==> v <= max_x;
    assert min_y in combined_y;
    assert forall v :: v in combined_y ==> v >= min_y;

    if max_x < min_y {
        result := "No War";
    } else {
        result := "War";
    }
}
