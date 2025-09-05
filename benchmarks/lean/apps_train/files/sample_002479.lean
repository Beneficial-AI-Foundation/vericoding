=====Function Descriptions=====
mean

The mean tool computes the arithmetic mean along the specified axis.

import numpy

my_array = numpy.array([ [1, 2], [3, 4] ])

print numpy.mean(my_array, axis = 0)        #Output : [ 2.  3.]
print numpy.mean(my_array, axis = 1)        #Output : [ 1.5  3.5]
print numpy.mean(my_array, axis = None)     #Output : 2.5
print numpy.mean(my_array)                  #Output : 2.5

By default, the axis is None. Therefore, it computes the mean of the flattened array.

var

The var tool computes the arithmetic variance along the specified axis.

import numpy

my_array = numpy.array([ [1, 2], [3, 4] ])

print numpy.var(my_array, axis = 0)         #Output : [ 1.  1.]
print numpy.var(my_array, axis = 1)         #Output : [ 0.25  0.25]
print numpy.var(my_array, axis = None)      #Output : 1.25
print numpy.var(my_array)                   #Output : 1.25

By default, the axis is None. Therefore, it computes the variance of the flattened array.

std

The std tool computes the arithmetic standard deviation along the specified axis.

import numpy

my_array = numpy.array([ [1, 2], [3, 4] ])

print numpy.std(my_array, axis = 0)         #Output : [ 1.  1.]
print numpy.std(my_array, axis = 1)         #Output : [ 0.5  0.5]
print numpy.std(my_array, axis = None)      #Output : 1.118033988749895
print numpy.std(my_array)                   #Output : 1.118033988749895

By default, the axis is None. Therefore, it computes the standard deviation of the flattened array.

=====Problem Statement=====
You are given a 2-D array of size NXM.
Your task is to find:
The mean along axis 1
The var along axis 0
The std along axis None

=====Input Format=====
The first line contains the space separated values of N and M.
The next N lines contains M space separated integers.

=====Output Format=====
First, print the mean.
Second, print the var.
Third, print the std.

def Matrix := Array (Array Float)

def getRow (A : Matrix) (i : Nat) : Array Float := sorry

def getCol (A : Matrix) (j : Nat) : Array Float := sorry
def mean (A : Matrix) : Array Float := sorry

def var (A : Matrix) : Array Float := sorry
def std (A : Matrix) : Float := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded