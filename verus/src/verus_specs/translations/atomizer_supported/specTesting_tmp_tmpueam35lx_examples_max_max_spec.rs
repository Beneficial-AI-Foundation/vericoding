use vstd::prelude::*;

verus! {

// ATOM 
pub fn max(a: int, b: int) -> (m: int)
    ensures
        m >= a,
        m >= b,
        m == a || m == b,
{
}

// ATOM 

pub open spec fn post_max(a: int, b: int, m: int) -> bool
{
    && m >= a
    && m >= b
    && (m == a || m == b)
}

// to check if it is functioning: postcondition not too accommodating
// the case it will refuse
// ATOM 

// an equivalent way of doing so
pub proof fn post_max_point_1_prime(a: int, b: int, m: int)
    requires
        a > b,
        post_max(a, b, m),
    ensures
        m == a,
{
}

// an equivalent way of doing so

// ATOM 

pub proof fn post_max_point_2(a: int, b: int, m: int)
    requires
        a == b,
        m != a || m != b,
    ensures
        !post_max(a, b, m),
{
}

// ATOM 

pub proof fn post_max_point_3(a: int, b: int, m: int)
    requires
        a < b,
        m != b,
    ensures
        !post_max(a, b, m),
{
}

// ATOM 

pub proof fn post_max_vertical_1_prime(a: int, b: int, m: int)
    requires
        post_max(a, b, m),
    ensures
        m == a || m == b,
{
}

// to check if it is implementable
// ATOM 

// to check if it is implementable
pub proof fn post_max_realistic_1(a: int, b: int, m: int)
    requires
        a > b,
        m == a,
    ensures
        post_max(a, b, m),
{
}

// ATOM 

pub proof fn post_max_realistic_2(a: int, b: int, m: int)
    requires
        a < b,
        m == b,
    ensures
        post_max(a, b, m),
{
}

// ATOM 

pub proof fn post_max_realistic_3(a: int, b: int, m: int)
    requires
        a == b,
        m == a,
    ensures
        post_max(a, b, m),
{
}

// this form is more natural
// ATOM 

pub proof fn max_deterministic_prime(a: int, b: int, m: int, m_prime: int)
    requires
        m != m_prime,
    ensures
        !post_max(a, b, m) || !post_max(a, b, m_prime),
{
}

// ATOM 

pub proof fn lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper6Helper<T>(
        s: Seq<int>,
        b: int,
        i: nat
    )
    requires
        s.len() > i,
        b == s[i as int],
    ensures
        s.subrange(0, i as int) + seq![b] == s.subrange(0, (i + 1) as int),
{
}

// ATOM 

pub proof fn multisetEquality(m1: Multiset<int>, m2: Multiset<int>, m3: Multiset<int>, m4: Multiset<int>)
   requires
       m1 > m2 + m3,
       m1 == m2 + m4,
   ensures
       m3 < m4,
{
}

}