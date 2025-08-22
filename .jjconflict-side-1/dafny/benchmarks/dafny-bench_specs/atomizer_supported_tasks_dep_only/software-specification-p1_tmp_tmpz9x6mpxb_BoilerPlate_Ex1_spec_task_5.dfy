//ATOM_PLACEHOLDER_Tree//ATOM_PLACEHOLDER_Code//ATOM_PLACEHOLDER_serialise

// Ex 1
// ATOM 

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


// ATOM 

function deserialise<T>(s:seq<Code<T>>):seq<Tree<T>>
  requires |s| > 0
{
  deserialiseAux(s, [])
}


// Ex 2
//ATOM_PLACEHOLDER_testSerializeWithASingleLeaf

//ATOM_PLACEHOLDER_testSerializeNullValues

//ATOM_PLACEHOLDER_testSerializeWithAllElements

// Ex 3 

//ATOM_PLACEHOLDER_testDeseraliseWithASingleLeaf

// SPEC 

method testDeserializeWithASingleNode()
{
}


//ATOM_PLACEHOLDER_testDeserialiseWithAllElements

// Ex 4 
//ATOM_PLACEHOLDER_SerialiseLemma


//ATOM_PLACEHOLDER_DeserialisetAfterSerialiseLemma



