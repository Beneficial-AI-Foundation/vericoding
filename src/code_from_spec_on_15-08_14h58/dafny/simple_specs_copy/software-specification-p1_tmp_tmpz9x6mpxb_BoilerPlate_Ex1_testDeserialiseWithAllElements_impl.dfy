datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)


//ATOM

datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)


//ATOM

// Ex 1
function deserialiseAux<T>(codes: seq<Code<T>>, trees: seq<Tree<T>>): seq<Tree<T>>
 requires |codes| > 0 || |trees| > 0
 ensures |deserialiseAux(codes, trees)| >= 0
{
 if |codes| == 0 then trees
 else
  match codes[0] {
   case CLf(v) => deserialiseAux(codes[1..], trees + [Leaf(v)])
   case CSNd(v) => if (|trees| >= 1) then deserialiseAux(codes[1..], trees[..|trees|-1] + [SingleNode(v, trees[|trees|-1])]) else trees
   case CDNd(v) => if (|trees| >= 2) then deserialiseAux(codes[1..], trees[..|trees|-2] + [DoubleNode(v, trees[|trees|-1], trees[|trees|-2])]) else trees
  }
}


//ATOM

function deserialise<T>(s:seq<Code<T>>):seq<Tree<T>>
 requires |s| > 0
{
 deserialiseAux(s, [])
}


//IMPL

/* code modified by LLM (iteration 4): Simplified lemma to avoid timeout issues */
lemma DeserialiseAuxPropertiesLemma<T>(codes: seq<Code<T>>, trees: seq<Tree<T>>)
    requires |codes| > 0 || |trees| > 0
    ensures |deserialiseAux(codes, trees)| >= |trees|
    decreases |codes|
{
    if |codes| == 0 {
        // Base case: result is trees
    } else {
        match codes[0] {
            case CLf(v) => 
                // Adding a leaf increases the tree count
                DeserialiseAuxPropertiesLemma(codes[1..], trees + [Leaf(v)]);
            case CSNd(v) => 
                if |trees| >= 1 {
                    // SingleNode keeps the same count
                    DeserialiseAuxPropertiesLemma(codes[1..], trees[..|trees|-1] + [SingleNode(v, trees[|trees|-1])]);
                }
                // If |trees| < 1, returns trees unchanged
            case CDNd(v) => 
                if |trees| >= 2 {
                    // DoubleNode decreases count by 1
                    DeserialiseAuxPropertiesLemma(codes[1..], trees[..|trees|-2] + [DoubleNode(v, trees[|trees|-1], trees[|trees|-2])]);
                }
                // If |trees| < 2, returns trees unchanged
        }
    }
}

/* code modified by LLM (iteration 4): Simple lemma for leaf-only sequences */
lemma DeserialiseLeafOnlyLemma<T>(codes: seq<Code<T>>)
    requires |codes| > 0
    requires forall i :: 0 <= i < |codes| ==> codes[i].CLf?
    ensures |deserialise(codes)| == |codes|
    decreases |codes|
{
    if |codes| == 1 {
        // Base case: single leaf
        assert deserialise(codes) == deserialiseAux(codes, []);
    } else {
        var firstCode := codes[0];
        assert firstCode.CLf?;
        var restCodes := codes[1..];
        assert forall i :: 0 <= i < |restCodes| ==> restCodes[i].CLf?;
        DeserialiseLeafOnlyLemma(restCodes);
    }
}

method testDeserialiseWithAllElements()
    /* code modified by LLM (iteration 4): Fixed ensures clauses with proper preconditions */
    ensures var codes := [CLf(1), CLf(2), CDNd(3), CLf(4), CSNd(5)]; |codes| > 0 ==> |deserialise(codes)| > 0;
    ensures var leafCodes := [CLf(10), CLf(20)]; |leafCodes| > 0 ==> |deserialise(leafCodes)| == 2;
    ensures var singleCode := [CLf(42)]; |singleCode| > 0 ==> |deserialise(singleCode)| == 1;
{
    // Test with a sequence that uses all three code types
    var codes := [CLf(1), CLf(2), CDNd(3), CLf(4), CSNd(5)];
    assert |codes| > 0;
    var result := deserialise(codes);
    
    /* code modified by LLM (iteration 4): Use simplified lemma */
    DeserialiseAuxPropertiesLemma(codes, []);
    assert |result| > 0;
    
    // Test with just leaf codes
    var leafCodes := [CLf(10), CLf(20)];
    assert |leafCodes| > 0;
    assert forall i :: 0 <= i < |leafCodes| ==> leafCodes[i].CLf?;
    var leafResult := deserialise(leafCodes);
    DeserialiseLeafOnlyLemma(leafCodes);
    assert |leafResult| == 2;
    
    // Test with single element
    var singleCode := [CLf(42)];
    assert |singleCode| > 0;
    assert forall i :: 0 <= i < |singleCode| ==> singleCode[i].CLf?;
    var singleResult := deserialise(singleCode);
    DeserialiseLeafOnlyLemma(singleCode);
    assert |singleResult| == 1;
}