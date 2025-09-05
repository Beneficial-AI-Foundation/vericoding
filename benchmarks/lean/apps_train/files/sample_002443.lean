=====Function Descriptions=====
inner

The inner tool returns the inner product of two arrays.

import numpy

A = numpy.array([0, 1])
B = numpy.array([3, 4])

print numpy.inner(A, B)     #Output : 4

outer

The outer tool returns the outer product of two arrays.

import numpy

A = numpy.array([0, 1])
B = numpy.array([3, 4])

print numpy.outer(A, B)     #Output : [[0 0]
                            #          [3 4]]

=====Problem Statement=====
You are given two arrays: A and B.
Your task is to compute their inner and outer product.

=====Input Format=====
The first line contains the space separated elements of array A.
The second line contains the space separated elements of array B.

=====Output Format=====
First, print the inner product.
Second, print the outer product.

def inner_product (v1 v2 : Vec Int) : Int := sorry 

def outer_product (v1 v2 : Vec Int) : Vec (Vec Int) := sorry

def vec_length {α : Type} (v : Vec α) : Nat :=
  match v with
  | Vec.nil => 0
  | Vec.cons _ rest => 1 + vec_length rest

def vec_sum_squares (v : Vec Int) : Int := sorry

def vec_transpose (m : Vec (Vec Int)) : Vec (Vec Int) := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded