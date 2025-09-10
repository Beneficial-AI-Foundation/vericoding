function concat_seqs(seqs: seq<seq<char>>): seq<char>
{
    if |seqs| == 0 then []
    else seqs[0] + concat_seqs(seqs[1..])
}

predicate ValidSplit(result: seq<seq<char>>, k: int, q: seq<char>)
{
    |result| == k &&
    (forall i :: 0 <= i < |result| ==> |result[i]| > 0) &&
    (forall i, j :: 0 <= i < j < |result| ==> result[i][0] != result[j][0]) &&
    concat_seqs(result) == q
}

// <vc-helpers>
lemma concat_seqs_empty()
    ensures concat_seqs([]) == []
{
}

lemma concat_seqs_single(s: seq<char>)
    ensures concat_seqs([s]) == s
{
}

lemma concat_seqs_append(seqs: seq<seq<char>>, s: seq<char>)
    ensures concat_seqs(seqs + [s]) == concat_seqs(seqs) + s
{
    if |seqs| == 0 {
        assert seqs + [s] == [s];
        concat_seqs_single(s);
    } else {
        assert seqs[0] == (seqs + [s])[0];
        assert seqs[1..] + [s] == (seqs + [s])[1..];
        concat_seqs_append(seqs[1..], s);
    }
}

function group_by_first_char(q: seq<char>): seq<seq<char>>
{
    if |q| == 0 then []
    else
        var first := q[0];
        var prefix := take_while_first_char(q, first);
        var rest := q[|prefix|..];
        [prefix] + group_by_first_char(rest)
}

function take_while_first_char(q: seq<char>, c: char): seq<char>
    requires |q| > 0
    requires q[0] == c
{
    if |q| == 1 then q
    else if q[1] == c then [q[0]] + take_while_first_char(q[1..], c)
    else [q[0]]
}

lemma take_while_properties(q: seq<char>, c: char)
    requires |q| > 0
    requires q[0] == c
    ensures var prefix := take_while_first_char(q, c);
            |prefix| > 0 && prefix[0] == c
    ensures var prefix := take_while_first_char(q, c);
            |prefix| <= |q|
    ensures var prefix := take_while_first_char(q, c);
            prefix == q[0..|prefix|]
{
}

lemma group_by_properties(q: seq<char>)
    ensures var groups := group_by_first_char(q);
            concat_seqs(groups) == q
    ensures var groups := group_by_first_char(q);
            forall i :: 0 <= i < |groups| ==> |groups[i]| > 0
    ensures var groups := group_by_first_char(q);
            forall i, j :: 0 <= i < j < |groups| ==> groups[i][0] != groups[j][0]
{
    if |q| == 0 {
        assert group_by_first_char(q) == [];
        concat_seqs_empty();
    } else {
        var first := q[0];
        var prefix := take_while_first_char(q, first);
        var rest := q[|prefix|..];
        var groups := group_by_first_char(q);
        
        take_while_properties(q, first);
        assert prefix == q[0..|prefix|];
        assert rest == q[|prefix|..];
        assert q == prefix + rest;
        
        group_by_properties(rest);
        concat_seqs_append([prefix], group_by_first_char(rest));
    }
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, q: seq<char>) returns (result: seq<seq<char>>)
    requires k >= 0
    requires |q| >= 0
    ensures k <= 0 || |q| == 0 ==> |result| == 0
    ensures k > 0 && |q| > 0 ==> (
        (|result| == 0) || ValidSplit(result, k, q)
    )
// </vc-spec>
// <vc-code>
{
    if k <= 0 || |q| == 0 {
        result := [];
        return;
    }
    
    var groups := group_by_first_char(q);
    group_by_properties(q);
    
    if |groups| == k {
        result := groups;
        assert ValidSplit(result, k, q);
    } else {
        result := [];
    }
}
// </vc-code>

