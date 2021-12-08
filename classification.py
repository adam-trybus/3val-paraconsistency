#!/usr/bin/env python
# coding: utf-8
from math import *
import itertools
from decimal import Decimal
from collections import Counter

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

# as defined in sette's logic	
def por_sette(con,A,B):
	return c(con,c(con,A,n(con,n(con,A))),c(con,n(con,A),B))

def pand(con,A,B):
	return n(con,por(con,n(con,A),n(con,B)))

# as defined in sette's logic
def pand_sette(con,A,B):
	return c(con,c(con,c(con,c(con,A,A),A), n(con,c(con,c(con,B,B),B))),n(con,c(con,A,n(con,B))))

def peq(con,A,B):
	return pand(con,c(con,A,B),c(con,B,A))

# as defined in sette's logic
def peq_sette(con,A,B):
	return pand_sette(con,c(con,A,B),c(con,B,A))

#checks which formulas are satisfied given an interpretation 'con' for connectives

def value(con):
	#standard classical axioms
	ax1 = c(con,vble(a,2),c(con,vble(b,2),vble(a,2)))
	ax2 = c(con,c(con,vble(a,3),c(con,vble(b,3),vble(d,3))),c(con,c(con,vble(a,3),vble(b,3)),c(con,vble(a,3),vble(d,3))))
	ax3 = c(con,c(con,vble(a,2),vble(b,2)),c(con,n(con,vble(b,2)),n(con,vble(a,2))))#
	ax4 = c(con,n(con,n(con,vble(a,2))),vble(a,2))
	ax5 = c(con,vble(a,2),n(con,n(con,vble(a,2))))
	ax6 = c(con,pand(con,vble(a,2),vble(b,2)),vble(a,2))
	ax7 = c(con,pand(con,vble(a,2),vble(b,2)),vble(b,2))
	ax8 = c(con,c(con,vble(a,3),vble(b,3)),c(con,c(con,vble(a,3),vble(d,3)),c(con,vble(a,3),pand(con,vble(b,3),vble(d,3)))))
	ax9 = c(con,vble(a,2),por(con,vble(a,2),vble(b,2)))#
	ax10 = c(con,vble(b,2),por(con,vble(a,2),vble(b,2)))
	ax11 = c(con,c(con,vble(a,3),vble(d,3)),c(con,c(con,vble(b,3),vble(d,3)),c(con,por(con,vble(a,3),vble(b,3)),vble(d,3))))
	ax12 = c(con,peq(con, vble(a,2),vble(b,2)),c(con, vble(a,2),vble(b,2)))
	ax13 = c(con,peq(con, vble(a,2),vble(b,2)),c(con, vble(b,2),vble(a,2)))
	ax14 = c(con,c(con, vble(a,2),vble(b,2)),c(con,c(con, vble(b,2),vble(a,2)),peq(con, vble(a,2),vble(b,2))))
	# axioms involving only negation and implication (ax1 above should be added as well)
	ax_1 = c(con,vble(a,2),c(con,vble(b,2),vble(a,2)))
	ax_2 = c(con,c(con,vble(a,3),c(con,vble(b,3),vble(d,3))),c(con,c(con,vble(a,3),vble(b,3)),c(con,vble(a,3),vble(d,3))))
	ax_3 = c(con,c(con,n(con,vble(a,2)),n(con,vble(b,2))),c(con,vble(b,2),vble(a,2)))#
	#axioms of the non-negation fragment of CL (positive)
	#pos1 = c(con,pand(con,vble(a,2),vble(b,2)),vble(a,2))
	#pos2 = c(con,pand(con,vble(a,2),vble(b,2)),vble(b,2))
	#pos3 = c(con,vble(a,2),c(con,vble(b,2),pand(con,vble(a,2),vble(b,2))))
	#pos4 = c(con,vble(a,2),por(con,vble(a,2),vble(b,2)))
	#pos5 = c(con,vble(b,2),por(con,vble(a,2),vble(b,2)))
	#pos6 = c(con,c(con,vble(a,3),vble(d,3)), c(con,c(con,vble(b,3),vble(d,3)), c(con,por(con,vble(a,3),vble(b,3)),vble(d,3))))
	#implicational fragment formulas
	imp1 = c(con,vble(a,1),vble(a,1))
	imp2 = c(con,c(con,vble(b,3),vble(d,3)),c(con,c(con,vble(a,3),vble(b,3)),c(con,vble(a,3),vble(d,3))))
	imp3 = c(con,c(con,vble(a,3),c(con,vble(b,3),vble(d,3))),c(con,vble(b,3),c(con,vble(a,3),vble(d,3))))
	imp4 = c(con,c(con,vble(a,3),c(con,vble(a,3),vble(b,3))),c(con,vble(a,3),vble(b,3)))
	imp5 = c(con,c(con,vble(a,3),vble(b,3)),c(con,vble(d,3),c(con,vble(a,3),vble(b,3))))
	# axioms of hilbert PC with connectives defined using sette's idea:
	ax1s = c(con,vble(a,2),c(con,vble(b,2),vble(a,2)))
	ax2s = c(con,c(con,vble(a,3),c(con,vble(b,3),vble(d,3))),c(con,c(con,vble(a,3),vble(b,3)),c(con,vble(a,3),vble(d,3))))
	ax3s = c(con,c(con,vble(a,2),vble(b,2)),c(con,n(con,vble(b,2)),n(con,vble(a,2))))#
	ax4s = c(con,n(con,n(con,vble(a,2))),vble(a,2))
	ax5s = c(con,vble(a,2),n(con,n(con,vble(a,2))))
	ax6s = c(con,pand_sette(con,vble(a,2),vble(b,2)),vble(a,2))
	ax7s = c(con,pand_sette(con,vble(a,2),vble(b,2)),vble(a,2))#c_sette(pand_sette(vble(a,2),vble(b,2)),vble(b,2))
	ax8s = c(con,c(con,vble(a,3),vble(b,3)),c(con,c(con,vble(a,3),vble(d,3)),c(con,vble(a,3),pand_sette(con,vble(b,3),vble(d,3)))))#only 168?
	ax9s = c(con,vble(a,2),por_sette(con,vble(a,2),vble(b,2)))#
	ax10s = c(con,vble(b,2),por_sette(con,vble(a,2),vble(b,2)))
	ax11s = c(con,c(con,vble(a,3),vble(d,3)),c(con,c(con,vble(b,3),vble(d,3)),c(con,por_sette(con,vble(a,3),vble(b,3)),vble(d,3))))
	ax12s = c(con,peq_sette(con,vble(a,2),vble(b,2)),c(con,vble(a,2),vble(b,2)))
	ax13s = c(con,peq_sette(con,vble(a,2),vble(b,2)),c(con,vble(b,2),vble(a,2)))
	ax14s = c(con,c(con,vble(a,2),vble(b,2)),c(con,c(con,vble(b,2),vble(a,2)),peq_sette(con,vble(a,2),vble(b,2))))

	#compl = c(con,c(con, vble(b,2),vble(b,2)), c(con, vble(a,2),vble(b,2)) )
	# uncomment a selected option to obtain results for sets of axioms as used in the article
	#formula = ['cprhb',ax1,ax2,ax3,ax4,ax5,ax6,ax7,ax8,ax9,ax10,ax11,ax12,ax13,ax14]
	#formula = ['cprs',ax1, ax_1,ax_2,ax_3]
	#formula = ['ppr',pos1,pos2,pos3,pos4,pos5,pos6]
	#formula = ['cprsette',ax1s,ax2s,ax3s,ax4s,ax5s,ax6s,ax7s,ax8s,ax9s,ax10s,ax11s,ax12s,ax13s,ax14s]
	#formula = ['impcl',imp1,imp2,imp3,imp4,imp5]
	result = []
	for i in formula[1:]:
		if 0 in i:
			result.append('N')
		else:
			#if 0.5 not in i:
			#	print 'hooray'
			result.append('Y')
	return result

# neg star = star

#print value([0,1,0.5,1,0,1,1,1,1,1,0,1]) #4
#print value([0,1,0.5,1,0,1,1,1,1,1,0,0.5]) #6
#print value([0,1,0.5,1,0,1,1,1,1,0.5,0,1]) #22
#print value([0,1,0.5,1,0,1,1,1,1,0.5,0,0.5]) #24
#print value([0,1,0.5,1,0,1,1,1,0.5,1,0,1]) #58
#print value([0,1,0.5,1,0,1,1,1,0.5,1,0,0.5]) #60
#print value([0,1,0.5,1,0,1,1,1,0.5,0.5,0,1])#76
#print value([0,1,0.5,1,0,1,1,1,0.5,0.5,0,0.5]) #78
#print value([0,1,0.5,1,0,1,1,0.5,1,1,0,1]) #166
#print value([0,1,0.5,1,0,1,1,0.5,1,1,0,0.5]) #168
#print value([0,1,0.5,1,0,1,1,0.5,1,0.5,0,1]) #184
#print value([0,1,0.5,1,0,1,1,0.5,1,0.5,0,0.5]) #186
#print value([0,1,0.5,1,0,1,1,0.5,0.5,1,0,1]) #220
#print value([0,1,0.5,1,0,1,1,0.5,0.5,1,0,0.5]) #222
#print value([0,1,0.5,1,0,1,1,0.5,0.5,0.5,0,1]) #238
#print value([0,1,0.5,1,0,1,1,0.5,0.5,0.5,0,0.5]) #240
#print value([0,1,0.5,1,0,1,1,0,1,1,0,1]) #85
#print value([0,1,0.5,1,0,1,1,0,1,1,0,0]) #86
#print value([0,1,0.5,1,0,1,1,0,1,1,0,0.5]) #87

# neg star = one

#print value([0,1,1,1,0,1,1,1,1,1,0,1]) #4
#print value([0,1,1,1,0,1,1,1,1,1,0,0.5]) #6
#print value([0,1,1,1,0,1,1,1,1,0.5,0,1]) #22
#print value([0,1,1,1,0,1,1,1,1,0.5,0,0.5]) #24
#print value([0,1,1,1,0,1,1,1,0.5,1,0,1]) #58
#print value([0,1,1,1,0,1,1,1,0.5,1,0,0.5]) #60
#print value([0,1,1,1,0,1,1,1,0.5,0.5,0,1])#76
#print value([0,1,1,1,0,1,1,1,0.5,0.5,0,0.5]) #78
#print value([0,1,1,1,0,1,1,0.5,1,1,0,1]) #166
#print value([0,1,1,1,0,1,1,0.5,1,1,0,0.5]) #168
#print value([0,1,1,1,0,1,1,0.5,1,0.5,0,1]) #184
#print value([0,1,1,1,0,1,1,0.5,1,0.5,0,0.5]) #186
#print value([0,1,1,1,0,1,1,0.5,0.5,1,0,1]) #220
#print value([0,1,1,1,0,1,1,0.5,0.5,1,0,0.5]) #222
#print value([0,1,1,1,0,1,1,0.5,0.5,0.5,0,1]) #238
#print value([0,1,1,1,0,1,1,0.5,0.5,0.5,0,0.5]) #240
#print value([0,1,1,1,0,1,1,0,1,1,0,1]) #85
#print value([0,1,1,1,0,1,1,0,1,1,0,0]) #86
#print value([0,1,1,1,0,1,1,0,1,1,0,0.5]) #87



