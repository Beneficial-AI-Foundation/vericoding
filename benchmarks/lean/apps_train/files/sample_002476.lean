=====Function Descriptions=====
sum

The sum tool returns the sum of array elements over a given axis.

import numpy

my_array = numpy.array([ [1, 2], [3, 4] ])

print numpy.sum(my_array, axis = 0)         #Output : [4 6]
print numpy.sum(my_array, axis = 1)         #Output : [3 7]
print numpy.sum(my_array, axis = None)      #Output : 10
print numpy.sum(my_array)                   #Output : 10

By default, the axis value is None. Therefore, it performs a sum over all the dimensions of the input array.

prod

The prod tool returns the product of array elements over a given axis.

import numpy

my_array = numpy.array([ [1, 2], [3, 4] ])

print numpy.prod(my_array, axis = 0)            #Output : [3 8]
print numpy.prod(my_array, axis = 1)            #Output : [ 2 12]
print numpy.prod(my_array, axis = None)         #Output : 24
print numpy.prod(my_array)                      #Output : 24

By default, the axis value is None. Therefore, it performs the product over all the dimensions of the input array.

=====Problem Statement=====
ou are given a 2-D array with dimensions NXM.
Your task is to perform the sum tool over axis 0 and then find the product of that result.

=====Output Format=====
Compute the sum along axis 0. Then, print the product of that sum.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
