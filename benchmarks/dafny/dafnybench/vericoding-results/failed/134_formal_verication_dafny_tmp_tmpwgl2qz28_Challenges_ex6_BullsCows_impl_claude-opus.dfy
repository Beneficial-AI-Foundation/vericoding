// see pdf 'ex6 & 7 documentation' for excercise question

function bullspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{reccbull(s, u, 0)}

function cowspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{recccow(s, u, 0)}

function reccbull(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
decreases |s| - i
{
    if i ==|s| then 0
    else if s[i] == u[i] then reccbull(s, u, i + 1) + 1
    else reccbull(s, u, i + 1)
}

function recccow(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
decreases |s| - i
{
    if i == |s| then 0
    else if s[i] != u[i] && u[i] in s then recccow(s, u, i + 1) + 1
    else recccow(s, u, i + 1)
}

predicate nomultiples(u:seq<nat>) 
{forall j, k :: 0<=j<k<|u| ==> u[j] != u[k]}

// <vc-helpers>
lemma BullsLemma(s: seq<nat>, u: seq<nat>, i: nat)
    requires 0 <= i < |s| == |u|
    ensures reccbull(s, u, i) == (if s[i] == u[i] then 1 else 0) + reccbull(s, u, i + 1)
{
}

lemma CowsLemma(s: seq<nat>, u: seq<nat>, i: nat)
    requires 0 <= i < |s| == |u|
    ensures recccow(s, u, i) == (if s[i] != u[i] && u[i] in s then 1 else 0) + recccow(s, u, i + 1)
{
}

lemma BullsAccumulation(s: seq<nat>, u: seq<nat>, i: nat, acc: nat)
    requires 0 <= i <= |s| == |u|
    requires acc == reccbull(s[..i], u[..i], 0)
    ensures i < |s| ==> reccbull(s[..i+1], u[..i+1], 0) == acc + (if s[i] == u[i] then 1 else 0)
{
    if i < |s| {
        assert s[..i+1] == s[..i] + [s[i]];
        assert u[..i+1] == u[..i] + [u[i]];
        var s' := s[..i+1];
        var u' := u[..i+1];
        
        if i == 0 {
            assert s' == [s[0]];
            assert u' == [u[0]];
            calc {
                reccbull(s', u', 0);
            ==
                if s'[0] == u'[0] then 1 + reccbull(s', u', 1) else reccbull(s', u', 1);
            ==
                if s[0] == u[0] then 1 + 0 else 0;
            ==
                acc + (if s[i] == u[i] then 1 else 0);
            }
        } else {
            calc {
                reccbull(s', u', 0);
            == { assert |s'| == i + 1; assert i + 1 > 0; BullsPrefix(s', u', i); }
                reccbull(s'[..i], u'[..i], 0) + reccbull(s', u', i);
            == { assert s'[..i] == s[..i]; assert u'[..i] == u[..i]; }
                reccbull(s[..i], u[..i], 0) + reccbull(s', u', i);
            == { assert s'[i] == s[i]; assert u'[i] == u[i]; }
                acc + (if s[i] == u[i] then 1 else 0);
            }
        }
    }
}

lemma BullsPrefix(s: seq<nat>, u: seq<nat>, k: nat)
    requires 0 < k <= |s| == |u|
    ensures reccbull(s, u, 0) == reccbull(s[..k], u[..k], 0) + reccbull(s, u, k)
{
    if k == |s| {
        assert s[..k] == s;
        assert u[..k] == u;
    } else {
        BullsPrefixHelper(s, u, 0, k);
    }
}

lemma BullsPrefixHelper(s: seq<nat>, u: seq<nat>, i: nat, k: nat)
    requires 0 <= i <= k <= |s| == |u|
    ensures reccbull(s, u, i) == reccbull(s[..k], u[..k], i) + reccbull(s, u, k)
    decreases k - i
{
    if i == k {
        assert reccbull(s[..k], u[..k], i) == 0;
    } else {
        BullsPrefixHelper(s, u, i + 1, k);
    }
}

lemma CowsAccumulation(s: seq<nat>, u: seq<nat>, i: nat, acc: nat)
    requires 0 <= i <= |s| == |u|
    requires acc == recccow(s[..i], u[..i], 0)
    ensures i < |s| ==> recccow(s[..i+1], u[..i+1], 0) == acc + (if s[i] != u[i] && u[i] in s then 1 else 0)
{
    if i < |s| {
        assert s[..i+1] == s[..i] + [s[i]];
        assert u[..i+1] == u[..i] + [u[i]];
        var s' := s[..i+1];
        var u' := u[..i+1];
        
        if i == 0 {
            assert s' == [s[0]];
            assert u' == [u[0]];
            calc {
                recccow(s', u', 0);
            ==
                if s'[0] != u'[0] && u'[0] in s' then 1 + recccow(s', u', 1) else recccow(s', u', 1);
            ==
                if s[0] != u[0] && u[0] in s' then 1 + 0 else 0;
            == { assert u[0] in s' ==> u[0] in s; }
                if s[0] != u[0] && u[0] in s then 1 else 0;
            ==
                acc + (if s[i] != u[i] && u[i] in s then 1 else 0);
            }
        } else {
            calc {
                recccow(s', u', 0);
            == { assert |s'| == i + 1; assert i + 1 > 0; CowsPrefix(s', u', i); }
                recccow(s'[..i], u'[..i], 0) + recccow(s', u', i);
            == { assert s'[..i] == s[..i]; assert u'[..i] == u[..i]; }
                recccow(s[..i], u[..i], 0) + recccow(s', u', i);
            == { assert s'[i] == s[i]; assert u'[i] == u[i]; 
                 assert u[i] in s' ==> u[i] in s; }
                acc + (if s[i] != u[i] && u[i] in s' then 1 else 0);
            == { assert u[i] in s' ==> u[i] in s; }
                acc + (if s[i] != u[i] && u[i] in s then 1 else 0);
            }
        }
    }
}

lemma CowsPrefix(s: seq<nat>, u: seq<nat>, k: nat)
    requires 0 < k <= |s| == |u|
    ensures recccow(s, u, 0) == recccow(s[..k], u[..k], 0) + recccow(s, u, k)
{
    if k == |s| {
        assert s[..k] == s;
        assert u[..k] == u;
    } else {
        CowsPrefixHelper(s, u, 0, k);
    }
}

lemma CowsPrefixHelper(s: seq<nat>, u: seq<nat>, i: nat, k: nat)
    requires 0 <= i <= k <= |s| == |u|
    ensures recccow(s, u, i) == recccow(s[..k], u[..k], i) + recccow(s, u, k)
    decreases k - i
{
    if i == k {
        assert recccow(s[..k], u[..k], i) == 0;
    } else {
        CowsPrefixHelper(s, u, i + 1, k);
    }
}
// </vc-helpers>

// <vc-spec>
method BullsCows (s:seq<nat>, u:seq<nat>) returns (b:nat, c:nat) 
requires 0 < |u| == |s| <= 10
requires nomultiples(u) && nomultiples(s);
ensures b >= 0 && c >= 0
ensures b == bullspec(s, u)
ensures c == cowspec(s, u)
// </vc-spec>
// <vc-code>
{
    b := 0;
    c := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant b == reccbull(s[0..i], u[0..i], 0)
        invariant c == recccow(s[0..i], u[0..i], 0)
    {
        ghost var old_b := b;
        ghost var old_c := c;
        
        if s[i] == u[i] {
            b := b + 1;
        } else if u[i] in s {
            c := c + 1;
        }
        
        BullsAccumulation(s, u, i, old_b);
        CowsAccumulation(s, u, i, old_c);
        
        i := i + 1;
    }
    
    assert i == |s|;
    assert s[0..|s|] == s;
    assert u[0..|u|] == u;
    assert b == reccbull(s, u, 0);
    assert c == recccow(s, u, 0);
}
// </vc-code>

