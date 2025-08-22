// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//ATOM 
// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/* code modified by LLM (iteration 1): Added return expression to fix compilation error */
function M1(f:map<int, bool>, i:int):bool
{
    i in f && f[i]
}

//ATOM 
function M2(f:map<int, bool>, i:int):bool
{
    M1(map j | j in f :: f[j], i)
}

//IMPL L
lemma L(f:map<int, bool>, i:int)
    requires i in f;
    requires M2(f, i);
    requires forall j:int, f:map<int, bool> :: M1(f, j) == (j in f && f[j]);
{
    /* code modified by LLM (iteration 1): Added proof body to establish the lemma */
    var g := map j | j in f :: f[j];
    assert M2(f, i) == M1(g, i);
    assert M1(g, i) == (i in g && g[i]);
    assert i in g <==> i in f;
    if i in f {
        assert g[i] == f[i];
    }
}