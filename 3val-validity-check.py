#!/usr/bin/env python
# coding: utf-8
from math import *
import itertools
from decimal import Decimal
from collections import Counter
import operator

# This is a companion program for the article A. Trybus, 'A generalisation of a Refutation-related Method in Paraconsistent Logics', Logic and Logical Philosophy 2017. It is designed to be run as a BASH script. Tested on ubuntu. Enqiries: adam.trybus@gmail.com

# populates matrix with all the possible permutations of the initial values of 1)-5) in sub-classical implication matrices:
#     || 1 | 0 | 0.5
# ====||================
# 1   || 1 | 2 | 5 
# 0   || 3 | 4 | 6
# 0.5 || 7 | 8 | 9
#
# initialising variables (can be changed to yield other systems)
initial_three = [1,0,0.5]
iterations = 5

def populate_matrix(initial_values,iterations):
	final = []
	matrix = [x for x in itertools.product(initial_values,repeat=iterations)]
	for i in matrix:
		final.append([matrix.index(i)+1]+list(i))
	return final

# searches a list for items satisfying single condition and returns them

def search_single(liste, condition):
	sat = []
	for i in liste:
		if i[condition[0]] == condition[1]:
			sat.append(i)
	return sat
			

# searches list for items (here: matrices) satisfying multiple conditions and returns matrix numbers (return final) or implication matrices with numbers (return list1) of those that do

def search(liste, conditions):
	final = []
	list1 = liste
	if len(conditions) != 0:

		for j in conditions:
			list1 = search_single(list1, j)

	for i in list1:
		final.append(i[0])	
	#return list1
	return final

# strings everything together to find matrices satisfying certain conditions imposed on the values of their elements and returns their matrix numbers

def paraimp(matrix):
	# names star and one refer to the way, in which negation is defined. In the former case: not 0.5 = 0.5, in the latter: not 0.5 = 1
	para_star = {}
	para_one = {}
	# a general setting, this makes matrix satisfy condition (mp), can be turned off
	case1 = search(matrix,[[4,0]])
	#case1 = search(matrix,[])
	# final tallying up

	para1 = list(sorted(set(case1)))
	para2 = list(sorted(set(case1)))

	for i in para1:
		para_star[i] = [1,0,1,1] + matrix[i-1][1:]
	for i in para2:
		para_one[i] = [1,0,1,1] + matrix[i-1][1:]
	return para_star, para_one


# set up for propositional variables' valuations used in evaluating formulas

a = [[1,0,0.5],[1,1,0,0,1,0,0.5,0.5,0.5],[1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0.5,0.5,0.5,0.5,0.5,0.5,0.5,0.5,0.5]]
b = [[],[1,0,1,0,0.5,0.5,1,0,0.5],[1,1,1,0,0,0,0.5,0.5,0.5,1,1,1,0,0,0,0.5,0.5,0.5,1,1,1,0,0,0,0.5,0.5,0.5]]
d = [[],[],[1,0,0.5,1,0,0.5,1,0,0.5,1,0,0.5,1,0,0.5,1,0,0.5,1,0,0.5,1,0,0.5,1,0,0.5]]



def vble(name, no):
	if name == a:
		return a[no-1]
	elif name == b:
		return b[no-1]
	elif name == d:
		return d[no-1]

def n(con, A):
	result = []
	for i in range(len(A)):
		if A[i] == 0.5:
			result.append(con[2])
		elif A[i] == 1:
			result.append(con[0])
		elif A[i] == 0:
			result.append(con[1])	
	return result

def c(con, A, B):
	result = [0]*len(A)
	for i in range(len(A)):
		if A[i] == 1 and B[i] == 1:
			result[i] = con[3]
		elif A[i] == 1 and B[i] == 0:
			result[i] = con[4]
		elif A[i] == 0 and B[i] == 1:
			result[i] = con[5]
		elif A[i] == 0 and B[i] == 0:
			result[i] = con[6]
		elif A[i] == 1 and B[i] == 0.5:
			result[i] = con[7]
		elif A[i] == 0 and B[i] == 0.5:
			result[i] = con[8]
		elif A[i] == 0.5 and B[i] == 1:
			result[i] = con[9]
		elif A[i] == 0.5 and B[i] == 0:
			result[i] = con[10]
		elif A[i] == 0.5 and B[i] == 0.5:
			result[i] = con[11]
	return result

def por(con,A,B):
	return (c(con,n(con,A),B))			

def pand(con,A,B):
	return n(con,por(con,n(con,A),n(con,B)))

def peq(con,A,B):
	return pand(con,c(con,A,B),c(con,B,A))


# checks if the discussed axioms hold for the selected matrices (having the (mp) property)


def hilbert_axioms_score(con):
	ax1 = c(con,vble(a,2),c(con,vble(b,2),vble(a,2)))
	ax2 = c(con,c(con,vble(a,3),c(con,vble(b,3),vble(d,3))),c(con,c(con,vble(a,3),vble(b,3)),c(con,vble(a,3),vble(d,3))))
	ax3 = c(con,c(con,vble(a,2),vble(b,2)),c(con,n(con,vble(b,2)),n(con,vble(a,2))))
	ax4 = c(con,n(con,n(con,vble(a,2))),vble(a,2))
	ax5 = c(con,vble(a,2),n(con,n(con,vble(a,2))))
	ax6 = c(con,pand(con,vble(a,2),vble(b,2)),vble(a,2))
	ax7 = c(con,pand(con,vble(a,2),vble(b,2)),vble(b,2))
	ax8 = c(con,c(con,vble(a,3),vble(b,3)),c(con,c(con,vble(a,3),vble(d,3)),c(con,vble(a,3),pand(con,vble(b,3),vble(d,3)))))
	ax9 = c(con,vble(a,2),por(con,vble(a,2),vble(b,2)))
	ax10 = c(con,vble(b,2),por(con,vble(a,2),vble(b,2)))
	ax11 = c(con,c(con,vble(a,3),vble(d,3)),c(con,c(con,vble(b,3),vble(d,3)),c(con,por(con,vble(a,3),vble(b,3)),vble(d,3))))
	ax12 = c(con,peq(con, vble(a,2),vble(b,2)),c(con, vble(a,2),vble(b,2)))
	ax13 = c(con,peq(con, vble(a,2),vble(b,2)),c(con, vble(b,2),vble(a,2)))
	ax14 = c(con,c(con, vble(a,2),vble(b,2)),c(con,c(con, vble(b,2),vble(a,2)),peq(con, vble(a,2),vble(b,2))))
	formula = [ax1,ax2,ax3,ax4,ax5,ax6,ax7,ax8,ax9,ax10,ax11,ax12,ax13,ax14]
	result = 0
	for i in formula:
		if not 0 in i:
			result = result+1

	return result

def hilbert_axiom_check_score(matrix):
	star, one = paraimp(matrix)
	axioms_star = {}
	axioms_one = {}
	for i in star:
		star[i] = [0,1,0.5]+star[i]
		axioms_star[i] = hilbert_axioms_score(star[i])
	for i in one:
		one[i] = [0,1,1]+one[i]
		axioms_one[i] = hilbert_axioms_score(one[i])
	sorted_star = sorted(axioms_star.items(), key=operator.itemgetter(0))
	sorted_one = sorted(axioms_one.items(), key=operator.itemgetter(0))
	return sorted_star, sorted_one

#typical set-up for running the program

paramatrix = populate_matrix(initial_three,iterations)
star,one = hilbert_axiom_check_score(paramatrix)

## prints the results for matrices with negation defined not 0.5 = 0.5
print star

## prints the results for matrices with negation defined not 0.5 = 1
print one
