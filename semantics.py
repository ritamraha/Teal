from z3 import *
from signaltraces import Sample
from monitoring import *

#ensures if the tuples form a proper intervals
def ensureProperIntervals(itvs, num_itvs, end_time):

	max_int = len(itvs)

	cons = And([0<=num_itvs, num_itvs<=max_int, 0<=itvs[0][0]])

	for t in range(max_int):
					
		cons1 = Implies(t<num_itvs, itvs[t][0]<itvs[t][1])

		cons2 =  Implies(t>=num_itvs,
									And(itvs[t][0]==end_time,\
										itvs[t][1]==end_time))
				
		cons = And([cons1, cons2, cons])

		if t<max_int-1:					
			cons3 = itvs[t][1]<=itvs[t+1][0]
			cons = And([cons3, cons])

	return cons				


#semantics for the negation of itvs

def not_itv(itvs, neg_itvs, num_itv, new_num_itv, end_time):

	case1 = And([And(neg_itvs[0][0]==0, neg_itvs[0][1]==itvs[0][0])]+\
					[And(neg_itvs[i][0] == itvs[i-1][1], neg_itvs[i][1] == itvs[i][0]) for i in range(1,len(itvs))])
	case2 = And([And(neg_itvs[i][0]==itvs[i][1], neg_itvs[i][1]==itvs[i+1][0]) for i in range(len(itvs)-1)])

	cons1 = If(itvs[0][0] != 0, case1, case2)
	
	cons2 = And([Implies(neg_itvs[0][0]==end_time, new_num_itv==0)]+\
				[Implies(And(neg_itvs[i][0]==end_time, neg_itvs[i-1][0]!=end_time), new_num_itv==i) for i in range(1,len(itvs))])

	
	cons  =And([cons1, cons2])

	return cons

#semantics for taking "or" of two interval lists 
def or_itv(itvs1, itvs2, or_itvs, i, signal_id, num_itv1, num_itv2, new_num_itv, end_time):
	#optimize
	max_int = len(itvs1)
	
	
	cons1 = And([Implies(i<new_num_itv, Or([ Or(or_itvs[i][s]==itvs1[j][s], or_itvs[i][s]==itvs2[j][s])\
			  for j in range(max_int)])) for s in [0,1] for i in range(max_int)])
	
	#cons2 = And([Implies(i < new_num_itv, or_itvs[i][0] < or_itvs[i][1]) for i in range(len(itvs1))])
	
	cons3 = And([Implies(j<num_itv1,\
						Or([itvs1[j][0] == or_itvs[i][0] for i in range(max_int)])==\
							And([Or(itvs2[k][0]>=itvs1[j][0], itvs1[j][0]>itvs2[k][1]) for k in range(max_int)]))\
							 for j in range(max_int)])

	cons4 = And([Implies(j<num_itv1,\
						Or([itvs1[j][1] == or_itvs[i][1] for i in range(max_int)])==\
							And([Or(itvs2[k][0]>itvs1[j][1], itvs1[j][1]>=itvs2[k][1]) for k in range(max_int)]))\
							 for j in range(max_int)])

	cons5 = And([Implies(j<num_itv2,\
						Or([itvs2[j][0] == or_itvs[i][0] for i in range(max_int)])==\
							And([Or(itvs1[k][0]>=itvs2[j][0], itvs2[j][0]>itvs1[k][1]) for k in range(max_int)]))\
							 for j in range(max_int)])

	cons6 = And([Implies(j<num_itv2,\
						Or([itvs2[j][1] == or_itvs[i][1] for i in range(max_int)])==\
							And([Or(itvs1[k][0]>itvs2[j][1], itvs2[j][1]>=itvs1[k][1]) for k in range(max_int)]))\
							 for j in range(max_int)])
	

	
	cons = And([cons1, cons3, cons4, cons5, cons6])

	return cons
	

#semantics for taking "and" of two interval lists
def and_itv(itvs1, itvs2, and_itvs, i, signal_id, num_itv1, num_itv2, new_num_itv, end_time):

	neg_itvs1 = {t:(Real('neg_itv1_%d_%d_%d_0'%(i, signal_id, t)), Real('neg_itv1_%d_%d_%d_1'%(i, signal_id, t))) for t in range(len(itvs1))}
	neg_itvs2 = {t:(Real('neg_itv2_%d_%d_%d_0'%(i, signal_id, t)), Real('neg_itv2_%d_%d_%d_1'%(i, signal_id, t))) for t in range(len(itvs1))}
	neg_num_itvs1 = Int('neg_num_itv_1_%d_%d'%(i, signal_id))
	neg_num_itvs2 = Int('neg_num_itv_2_%d_%d'%(i, signal_id))

	cons1 = not_itv(itvs1, neg_itvs1, num_itv1, neg_num_itvs1, end_time)
	cons2 = not_itv(itvs2, neg_itvs2, num_itv2, neg_num_itvs2, end_time)

	or_itvs = {t:(Real('or_itv_%d_%d_%d_0'%(i, signal_id, t)), Real('or_itv_%d_%d_%d_1'%(i, signal_id, t))) for t in range(len(itvs1))}
	or_num_itvs = Int('or_num_itv_%d_%d'%(i, signal_id))

	cons3 = or_itv(neg_itvs1, neg_itvs2, or_itvs, i, signal_id, neg_num_itvs1, neg_num_itvs2, or_num_itvs, end_time)
	cons4 = not_itv(or_itvs, and_itvs, or_num_itvs, new_num_itv, end_time)

	cons5 = And([ensureProperIntervals(neg_itvs1, neg_num_itvs1,  end_time),\
		ensureProperIntervals(neg_itvs2, neg_num_itvs2, end_time), ensureProperIntervals(or_itvs, or_num_itvs, end_time)])

	cons = And([cons1, cons2, cons3, cons4, cons5])

	return cons



########################## Operator F ##########################	
#Given an interval list, a and b it returns an interval list with (lb-b, ub-a)
# def minus_itv(itvs, minus_itvs, a, b, i, signal_id, num_itv, new_num_itv, end_time):

# 	max_int = len(itvs)
# 	int_itvs = {t:(Real('minus_itvs_%d_%d_%d_0'%(i, signal_id, t)), \
# 					 Real('minus_itvs_%d_%d_%d_1'%(i, signal_id, t))) for t in range(len(itvs))}

# 	cons1 = And([If(i<num_itv, And(int_itvs[i][0]==If(itvs[i][0]>b, itvs[i][0]-b, 0),\
# 						int_itvs[i][1]==If(itvs[i][1]>a, itvs[i][1]-a, 0)),\
# 						And(int_itvs[i][0]==end_time, int_itvs[i][1]==end_time)) for i in range(max_int)])
	

# 	cons2 = And([And(minus_itvs[i][0]==int_itvs[i][0], minus_itvs[i][1]==int_itvs[i][1]) for i in range(max_int)])

# 	cons3 = new_num_itv==num_itv

# 	cons = And([cons1, cons2, cons3])

# 	return cons

def minus_itv(itvs, minus_itvs, a, b, i, signal_id, num_itv, new_num_itv, end_time):

	max_int = len(itvs)
	
	cons = (new_num_itv==num_itv +1)

	for i in range(max_int):

		cons1 = Implies(i<num_itv, And(minus_itvs[i][0]==If(itvs[i][0]>b, itvs[i][0]-b, 0),\
							minus_itvs[i][1]==If(itvs[i][1]>a, itvs[i][1]-a, 0)))
		
		cons2 = Implies(i==num_itv, And((minus_itvs[i][0]== end_time-a), (minus_itvs[i][1]==end_time)))	
		
		cons3 = Implies(i>num_itv, And(minus_itvs[i][0]==end_time, minus_itvs[i][1]==end_time))	

		#cons4 = And(minus_itvs[i][0]==int_itvs[i][0], minus_itvs[i][1]==int_itvs[i][1])

		cons = And([cons1, cons2, cons3, cons])

	return cons


#Given a list of intervals, output a list with their union
def union_itv(itvs, F_itvs, num_itv, new_num_itv, end_time):

	#ensuring interval bounds are from itvs
	cons1 = new_num_itv<=num_itv+1
	cons2 = And([Implies(i<= new_num_itv-1, Or([F_itvs[i][0]==itvs[j][0] for j in range(len(itvs))])) for i in range(len(itvs))])
	cons3 = And([Implies(i<= new_num_itv-1, Or([F_itvs[i][1]==itvs[j][1] for j in range(len(itvs))])) for i in range(len(itvs))])
	#cons4 = And([Implies(i <= new_num_itv-1, F_itvs[i][0] < F_itvs[i][1]) for i in range(len(itvs))])
	#cons5 = And([Implies(i > new_num_itv-1, And(F_itvs[i][0]==end_time, F_itvs[i][1]==end_time)) for i in range(len(itvs))])

	#ensuring all intervals are included
	cons6 = And([Implies(itvs[i][1]!=0,\
						Or([And(F_itvs[j][0] <= itvs[i][0], itvs[i][1]<= F_itvs[j][1]) for j in range(len(F_itvs))])) for i in range(len(itvs))])

	#ensuring no extra variables are included
	#cons7 = And([Implies(itvs[i][1] < itvs[j][0], Implies(And([Or((itvs[i][1]+itvs[j][0])/2<itvs[k][0],(itvs[i][1]+itvs[j][0])/2>itvs[k][1]) for k in range(len(itvs))]),\
	#						And([Or((itvs[i][1]+itvs[j][0])/2<F_itvs[l][0], (itvs[i][1]+itvs[j][0])/2>F_itvs[l][1]) for l in range(len(F_itvs))])))\
	#						for i in range(len(itvs)) for j in range(len(itvs))])

	cons7 = And([Implies(And(itvs[i][1] < itvs[i+1][0]), And([Or(((itvs[i][1] + itvs[i+1][0])/2)<F_itvs[j][0],\
															((itvs[i][1] + itvs[i+1][0])/2)>F_itvs[j][1]) \
						for j in range(len(F_itvs))])) for i in range(len(itvs)-1)])
	cons8 = And([Implies(i < new_num_itv-1, F_itvs[i][1] < F_itvs[i+1][0]) for i in range(len(itvs)-1)])


	cons = And([cons1, cons2, cons3, cons6, cons7, cons8])

	return cons

#semantics for operator F[a,b]
def F_itv(itvs, F_itvs, a, b, i, signal_id, num_itv, new_num_itv, end_time):

	minus_itvs = {t:(Real('minus_itvs_%d_%d_%d_0'%(i, signal_id, t)), Real('minus_itvs_%d_%d_%d_1'%(i, signal_id, t))) for t in range(len(itvs))}
	minus_num_itv = Int('minus_num_itv_%d_%d'%(i, signal_id))

	
	cons1 = minus_itv(itvs, minus_itvs, a, b, i, signal_id, num_itv, minus_num_itv, end_time)
	cons2 = union_itv(minus_itvs, F_itvs, minus_num_itv, new_num_itv, end_time)

	cons = And([cons1, cons2])

	return cons


def minus_G_itv(itvs, minus_itvs, a, b, i, signal_id, num_itv, new_num_itv, end_time):

	max_int = len(itvs)
	
	cons = Implies(num_itv==0, And([new_num_itv==1, minus_itvs[0][0]==end_time-a, minus_itvs[0][1]==end_time]))


	for i in range(max_int):

		cons1 = Implies(i<num_itv-1, And(minus_itvs[i][0]==If(itvs[i][0]>a, itvs[i][0]-a, 0),\
							minus_itvs[i][1]==If(itvs[i][1]>b, itvs[i][1]-b, 0)))
		
		cons2 = Implies(i>num_itv, And(minus_itvs[i][0]== end_time, minus_itvs[i][1]==end_time))

		if i<max_int-1:
			
			case1 = And([minus_itvs[i][1]==end_time, new_num_itv==num_itv,\
							minus_itvs[i+1][0]==end_time, minus_itvs[i+1][1]==end_time])
			case2 = And([minus_itvs[i][1]==itvs[i][1]-b, minus_itvs[i+1][0]==end_time-a, \
							minus_itvs[i+1][1]==end_time, new_num_itv==num_itv+1])

			cons3 = Implies(i==num_itv-1, And(minus_itvs[i][0]==If(itvs[i][0]>a, itvs[i][0]-a, 0),\
						If(itvs[i][1]==end_time, case1, case2)))

			cons=And([cons1, cons2, cons3, cons])
		
		else:
			
			cons=And([cons1, cons2, cons])
		

	return cons



def G_itv(itvs, G_itvs, a, b, i, signal_id, num_itv, new_num_itv, end_time):

	max_int = len(itvs)

	minus_itvs = {t:(Real('minus_itvs_G_%d_%d_%d_0'%(i, signal_id, t)), \
					Real('minus_itvs_G_%d_%d_%d_1'%(i, signal_id, t))) for t in range(max_int)}
	minus_num_itv = Int('minus_num_itv_G_%d_%d'%(i, signal_id))

	
	cons = minus_G_itv(itvs, minus_itvs, a, b, i, signal_id, num_itv, minus_num_itv, end_time)
	
	for i in range(max_int):
		
		cons1 = And([Or([And(G_itvs[i][0]==minus_itvs[j][0], G_itvs[i][1]==minus_itvs[j][1])\
									 for j in range(max_int)])])	
		cons2 = Implies(And([minus_itvs[i][0]!=G_itvs[j][0] for j in range(max_int)]),
							minus_itvs[i][0]>=minus_itvs[i][1])
		
		cons3 = Implies(i < new_num_itv, G_itvs[i][0] < G_itvs[i][1])

		cons = And([cons1, cons2, cons3, cons])

	return cons



#checking if the semantics is correct
def checking():

	#actual_itv1 = [(0,6),(11,12),(16,17),(20,20)]
	#actual_itv1 = [(0,6),(8,12),(16,17),(20,20)]
	#actual_itv1 = [(0, 1),(3, 5),(5, 5),(5, 5),(5, 5),(5, 5),(5, 5),(5, 5),(5, 5),(5, 5),(5, 5),(5, 5)]
	#actual_itv1 = [(2, 7),(8, 19),(20, 20),(20, 20)]
	s = Sample()
	s.readSample('./dummy.signal')
	for signal in s.positive:
		prop_itvs = compute_prop_intervals(signal, ['p','q'], {'p':0,'q':1}, 10.0)
		#print(prop_itvs)
		#actual_itv1 = prop_itvs['q'] + [(10.0,10.0)]*(6-len(prop_itvs['q']))
		actual_itv1 = [(10.0,10.0)] + [(10.0,10.0)]*5
		#actual_itv1 = [(3,5),(5,5),(5,5),(5,5),(5,5),(5,5),(5,5),(5,5),(5,5),(5,5),(5,5),(5,5)]
		nitv = compute_not_itvs(prop_itvs['p'], 10.0)
		actual_itv2 = nitv + [(10.0,10.0)]*(6-len(nitv))


		#[(13,14), (15.1,15.6), (7,15), (16,20)]
		#[(0,17), (20,20)]

		itv1 = {i:(Real('itv1_%d_0'%i), Real('itv1_%d_1'%i)) for i in range(len(actual_itv1))}
		itv2 = {i:(Real('itv2_%d_0'%i), Real('itv2_%d_1'%i)) for i in range(len(actual_itv2))}
		
		itv_new = {i:(Real('itv_new_%d_0'%i), Real('itv_new_%d_1'%i)) for i in range(len(actual_itv1))}

		num_itv1 = Int('num_itv_1')
		num_itv2 = Int('num_itv_2')
		a = Real('a')
		b = Real('b')
		new_num_itv = Int('new_num_itv')

		s = Solver()
		#s.add(itv_new[0][1] == 5)
		s.add(And([And(itv1[i][0]==actual_itv1[i][0], itv1[i][1]==actual_itv1[i][1]) for i in range(len(actual_itv1))]+[num_itv1==0, a==1, b==2]))#0.0625,1.9375
		s.add(And([And(itv2[i][0]==actual_itv2[i][0], itv2[i][1]==actual_itv2[i][1]) for i in range(len(actual_itv2))]+[num_itv2==len(nitv)]))

		s.add(ensureProperIntervals(itv_new, new_num_itv, 10.0))
		#s.add(minus_G_itv(itv1, itv_new, a, b, 0, 0, num_itv1, new_num_itv, 10.0))
		#s.add(self.or_itv(itv1, itv2, itv_new, num_itv1, num_itv2, new_num_itv, 20))
		s.add(G_itv(itv1, itv_new, a, b, 0, 0, num_itv1, new_num_itv, 10.0))
		#s.add(union_itv(itv1, itv_new, num_itv1, new_num_itv, 5))
		#s.add(minus_itv(itv1, itv_new, a, b, 0, 0, num_itv1, new_num_itv, 5))
		#s.add(or_itv(itv1, itv2, itv_new, 0, 0, num_itv1, num_itv2, new_num_itv, 10.0))
		#s.add(F_itv(itv1, itv_new, a, b, 0, 0, num_itv1, new_num_itv, 10.0))
		#s.add(not_itv(itv1, itv_new, num_itv1, new_num_itv, 10.0))
		#print(self.and_itv(itv1, itv2, itv_new, num_itv1, num_itv2, new_num_itv, 20))
		
		solverRes = s.check()
		print(solverRes)

		if solverRes == sat:
			solverModel = s.model()
			#print(solverModel)
			for i in range(len(actual_itv1)):
				print(i, (solverModel[itv_new[i][0]],solverModel[itv_new[i][1]]))
			#	print(i, solverModel[self.neg_itvs1[i][0]],solverModel[self.neg_itvs1[i][1]])
			print(solverModel[new_num_itv], solverModel[num_itv1])

#checking()

'''






[t1-a,t2-a] int [t1-b,t2-b]

[t1-a,t2-b]

[3,2)

[0,4) [0,5)

[5,6)
[2,4]

[3,6)[8,9)

[5,9)[10,12)
[2,3]












class SMTEncoding:

	def __init__(self):

		self.max_intervals = 10
		self.start_time = 0
		self.end_time = 20

		self.solver = Solver()

		

	def def_vars(self):
		# 0, 3, 4, 9
		self.initial_tp1 = [0, 2, 5, 6, 7, 9, 10, 10, 10]
		self.initial_tp2 = [0, 1, 3, 4, 8, 9, 10, 10, 10]
		self.max_intervals = len(self.initial_tp1)
		self.start_time = self.initial_tp1[0]
		self.end_time = self.initial_tp1[-1]

		self.s1 = {i:Real('s1_%d'%i) for i in range(1,self.max_intervals+1)}#dummy variables
		self.s2 = {i:Real('s2_%d'%i) for i in range(1,self.max_intervals+1)}#dummy variables
		self.t = {i:Real('t_%d'%i)for i in range(1,self.max_intervals+1)}#actual variables
		self.num_tp = Int('r')

		#Checking on some examples
		initial_cons = And([And(self.s1[i] == self.initial_tp1[i-1], self.s2[i] == self.initial_tp2[i-1]) for i in range(1,self.max_intervals+1)])
		self.solver.assert_and_track(initial_cons, 'Inital timepoints')

		if self.max_intervals%2 != 0:
			self.even_range = int((self.max_intervals-1)/2)
			self.odd_range = int((self.max_intervals+1)/2)
		else:
			self.even_range = int((self.max_intervals)/2)
			self.odd_range = int((self.max_intervals)/2)

# interval = {i:(Real('l_i'), Real('r_i') for i in range()}


	def find_sol(self):

		solverRes = self.solver.check()

		if solverRes == sat:
			solverModel = self.solver.model()
			print('SAT')
			for k in self.t:
				print('t_%d'%k, solverModel[self.t[k]])
			print('Num TP', solverModel[self.num_tp])
		else:
			checking= self.solver.unsat_core()
			print(checking)
			print('UNSAT')
	

	def ensureProperIntervals(self, itvs, end_time):

		max_int = len(itvs)

		cons1 = And([And(itvs[i][0]<=itvs[i][1], itvs[i][1]<=itvs[i+1][0]) for i in range(max_int-1)]\
						+[itvs[max_int-1][0]<=itvs[max_int-1][1]])

		cons2 = And(0<=itvs[0][0], itvs[max_int-1][1]<=end_time)
		#self.solver.add(cons3)

		cons = And([cons1, cons2])

		return cons

	########################## Operator Not ##########################
	def not_itv(self, itvs, neg_itvs, num_itv, new_num_itv, end_time):

		#optimize the for loops
		case1 = And([And(neg_itvs[0][0]==0, neg_itvs[0][1]==itvs[0][0])]+\
						[And(neg_itvs[i][0] == itvs[i-1][1], neg_itvs[i][1] == itvs[i][0]) for i in range(1,len(itvs))])
		case2 = And([And(neg_itvs[i][0]==itvs[i][1], neg_itvs[i][1]==itvs[i+1][0]) for i in range(len(itvs)-1)])

		cons1 = If(itvs[0][0] != 0, case1, case2)
		
		cons2 = And([Implies(And(neg_itvs[i][0]==end_time, neg_itvs[i-1][0]!=end_time), new_num_itv==i) for i in range(1,len(itvs))])

		cons3 = And([Implies(i >= new_num_itv, And(neg_itvs[i][0]==end_time, neg_itvs[i][1]==end_time)) for i in range(len(itvs))])

		cons  =And([cons1, cons2])

		return cons
	
	########################## Operator Or ##########################	
	def or_itv(self, itvs1, itvs2, or_itvs, num_itv1, num_itv2, new_num_itv, end_time):
		
		max_int = len(itvs1)
		#ensuring interval bounds are from either itvs1 or itvs2
		#cons1 = And(1<=new_num_itv, new_num_itv<=num_itv1+1)
		cons2 = And([Implies(i<new_num_itv, Or([ Or(or_itvs[i][0]==itvs1[j][0], or_itvs[i][0]==itvs2[j][0]) for j in range(len(itvs1))])) for i in range(len(itvs1))])
		cons3 = And([Implies(i<new_num_itv, Or([ Or(or_itvs[i][1]==itvs1[j][1], or_itvs[i][1]==itvs2[j][1]) for j in range(len(itvs1))])) for i in range(len(itvs1))])
		
		cons4 = And([Implies(i < new_num_itv, or_itvs[i][0] < or_itvs[i][1]) for i in range(len(itvs1))])
		cons5 = And([Implies(i > new_num_itv-1, And(or_itvs[i][0]==end_time, or_itvs[i][1]==end_time)) for i in range(len(itvs1))])

		
		#ensuring that intervals cannot be extended
		#cons6 = And([Implies(And(j+1<=num_itv1, or_itvs[i][0] == itvs1[j][0]),\
		#						And([Or(itvs2[k][0]>=itvs1[j][0], itvs1[j][0]>itvs2[k][1]) for k in range(len(itvs2))])) \
		#						for j in range(len(itvs1)) \
		#						for i in range(len(itvs1))])
		
		cons6 = And([Implies(j<num_itv1,\
							Or([itvs1[j][0] == or_itvs[i][0] for i in range(max_int)])==\
								And([Or(itvs2[k][0]>=itvs1[j][0], itvs1[j][0]>itvs2[k][1]) for k in range(max_int)]))\
								 for j in range(max_int)])

		cons7 = And([Implies(j<num_itv1,\
							Or([itvs1[j][1] == or_itvs[i][1] for i in range(max_int)])==\
								And([Or(itvs2[k][0]>itvs1[j][1], itvs1[j][1]>=itvs2[k][1]) for k in range(max_int)]))\
								 for j in range(max_int)])

		cons8 = And([Implies(j<num_itv2,\
							Or([itvs2[j][0] == or_itvs[i][0] for i in range(max_int)])==\
								And([Or(itvs1[k][0]>=itvs2[j][0], itvs2[j][0]>itvs1[k][1]) for k in range(max_int)]))\
								 for j in range(max_int)])

		cons9 = And([Implies(j<num_itv2,\
							Or([itvs2[j][1] == or_itvs[i][1] for i in range(max_int)])==\
								And([Or(itvs1[k][0]>itvs2[j][1], itvs2[j][1]>=itvs1[k][1]) for k in range(max_int)]))\
								 for j in range(max_int)])
		

		#og# cons6 = And([And([Implies(And(j+1<=num_itv1, or_itvs[i][0] == itvs1[j][0]),\
		#						And([Implies(k+1<=num_itv2, Not(And(itvs2[k][0]<itvs1[j][0], itvs1[j][0]<=itvs2[k][1]))) for k in range(len(itvs2))])) \
		#						for j in range(len(itvs1))]) \
		#
								for i in range(len(itvs1))])
		cons7 = And([Implies(And([i+1<=num_itv1]+[itvs1[i][0] != or_itvs[j][0] for j in range(len(or_itvs))]),
											Or([And(itvs2[k][0]<itvs1[i][0], itvs1[i][0]<=itvs2[k][1]) for k in range(len(itvs1))])) for i in range(len(itvs2))])
		
		cons8 = And([And([Implies(And(j+1<=num_itv1, or_itvs[i][1] == itvs1[j][1]),\
								And([Implies(k+1<=num_itv2, Not(And(itvs2[k][0]<=itvs1[j][1], itvs1[j][1]<itvs2[k][1]))) for k in range(len(itvs2))])) \
								for j in range(len(itvs1))]) \
								for i in range(len(itvs1))])
		cons9 = And([Implies(And([i+1<=num_itv1]+[itvs1[i][1] != or_itvs[j][1] for j in range(len(or_itvs))]),
											Or([And(itvs2[k][0]<=itvs1[i][1], itvs1[i][1]<itvs2[k][1]) for k in range(len(itvs1))])) for i in range(len(itvs2))])

		cons10 = And([And([Implies(And(j+1<=num_itv2, or_itvs[i][0] == itvs2[j][0]),\
								And([Implies(k+1<=num_itv1, Not(And(itvs1[k][0]<itvs2[j][0], itvs2[j][0]<=itvs1[k][1]))) for k in range(len(itvs2))])) \
								for j in range(len(itvs2))]) \
								for i in range(len(itvs2))])
		cons11 = And([Implies(And([i+1<=num_itv2]+[itvs2[i][0] != or_itvs[j][0] for j in range(len(or_itvs))]),
											Or([And(itvs1[k][0]<itvs2[i][0], itvs2[i][0]<=itvs1[k][1]) for k in range(len(itvs1))])) for i in range(len(itvs2))])


		cons12 = And([And([Implies(And(j+1<=num_itv2, or_itvs[i][1] == itvs2[j][1]),\
								And([Implies(k+1<=num_itv1, Not(And(itvs1[k][0]<=itvs2[j][1], itvs2[j][1]<itvs1[k][1]))) for k in range(len(itvs2))])) \
								for j in range(len(itvs2))]) \
								for i in range(len(itvs2))])
		
		cons13 = And([Implies(And([i+1<=num_itv2]+[itvs2[i][1] != or_itvs[j][1] for j in range(len(or_itvs))]),
											Or([And(itvs1[k][0]<=itvs2[i][1], itvs2[i][1]<itvs1[k][1]) for k in range(len(itvs1))])) for i in range(len(itvs2))])
		
		cons = And([cons2, cons3, cons4, cons5, cons6, cons7, cons8, cons9])

		return cons
	
	########################## Operator And ##########################
	def and_itv(self, itvs1, itvs2, and_itvs, num_itv1, num_itv2, new_num_itv, end_time):

		neg_itvs1 = {i:(Real('neg_itv1_%d_0'%i), Real('neg_itv1_%d_1'%i)) for i in range(len(itvs1))}
		neg_itvs2 = {i:(Real('neg_itv2_%d_0'%i), Real('neg_itv2_%d_1'%i)) for i in range(len(itvs1))}
		neg_num_itvs1 = Int('neg_num_itv_1')
		neg_num_itvs2 = Int('neg_num_itv_2')

		cons1 = self.not_itv(itvs1, neg_itvs1, num_itv1, neg_num_itvs1, end_time)
		cons2 = self.not_itv(itvs2, neg_itvs2, num_itv2, neg_num_itvs2, end_time)

		or_itvs = {i:(Real('or_itv_%d_0'%i), Real('or_itv_%d_1'%i)) for i in range(len(itvs1))}
		or_num_itvs = Int('or_num_itv')

		cons3 = self.or_itv(neg_itvs1, neg_itvs2, or_itvs, neg_num_itvs1, neg_num_itvs2, or_num_itvs, end_time)
		cons4 = self.not_itv(or_itvs, and_itvs, or_num_itvs, new_num_itv, end_time)

		cons5 = And([self.ensureProperIntervals(neg_itvs1, end_time),\
			self.ensureProperIntervals(neg_itvs2, end_time), self.ensureProperIntervals(or_itvs, end_time)])


		cons = And([cons1, cons2, cons3, cons4, cons5])

		return cons


	def minus_itv(self, itvs, minus_itvs, a, b, num_itv, new_num_itv, end_time):

		cons1 = And([Implies(i<new_num_itv,\
			Or([And([j<num_itv, \
				minus_itvs[i][0]==If(itvs[j][0]-b>0, itvs[j][0]-b, 0), minus_itvs[i][1]==If(itvs[j][1]>a, itvs[j][1]-a, 0)]) \
				for j in range(len(itvs)) ])) for i in range(len(itvs))])

		cons2 = And([Implies(And([i<num_itv]+[itvs[i][1]-a != minus_itvs[j][1] for j in range(len(itvs))]),\
							itvs[i][1] <= a)
							for i in range(len(itvs))])

		cons3 = And([minus_itvs[i][1]>0 for i in range(len(itvs))])

		cons4 = And([And(minus_itvs[i-1][0]<=minus_itvs[i][0], minus_itvs[i-1][1]<=minus_itvs[i][1])\
										 for i in range(1,len(itvs))]) 

		cons5 = And([Implies(i >= new_num_itv, \
					And(minus_itvs[i][0]==end_time, minus_itvs[i][1]==end_time)) for i in range(len(itvs))])

		cons = And([cons1, cons2, cons3, cons4, cons5])

		return cons



	########################## Operator F ##########################	
	def union_itv(self, itvs, F_itvs, num_itv, new_num_itv, end_time):


		#ensuring interval bounds are from itvs
		cons1 = new_num_itv<=num_itv+1
		cons2 = And([Implies(i<= new_num_itv-1, Or([F_itvs[i][0]==itvs[j][0] for j in range(len(itvs))])) for i in range(len(itvs))])
		cons3 = And([Implies(i<= new_num_itv-1, Or([F_itvs[i][1]==itvs[j][1] for j in range(len(itvs))])) for i in range(len(itvs))])
		cons4 = And([Implies(i <= new_num_itv-1, F_itvs[i][0] < F_itvs[i][1]) for i in range(len(itvs))])
		cons5 = And([Implies(i > new_num_itv-1, And(F_itvs[i][0]==end_time, F_itvs[i][1]==end_time)) for i in range(len(itvs))])


		#ensuring all intervals are included
		cons6 = And([Or([And(F_itvs[j][0] <= itvs[i][0], itvs[i][1]<= F_itvs[j][1]) for j in range(len(F_itvs))]) for i in range(len(itvs))])

		#ensuring no extra variables are included
		cons7 = And([Implies(itvs[i][1] < itvs[j][0], Implies(And([Or((itvs[i][1]+itvs[j][0])/2<itvs[k][0],(itvs[i][1]+itvs[j][0])/2>itvs[k][1]) for k in range(len(itvs))]),\
								And([Or((itvs[i][1]+itvs[j][0])/2<F_itvs[l][0], (itvs[i][1]+itvs[j][0])/2>F_itvs[l][1]) for l in range(len(F_itvs))])))\
								for i in range(len(itvs)) for j in range(len(itvs))])

		cons = And([cons1, cons2, cons3, cons4, cons5, cons6, cons7])

		return cons



	def F_itv(self, itvs, F_itvs, a, b, num_itv, new_num_itv, end_time):

		minus_itvs = {i:(Real('minus_itvs_%d_0'%i), Real('minus_itvs_%d_1'%i)) for i in range(len(itvs))}
		minus_num_itv = Int('minus_num_itv')
		cons1 = self.minus_itv(itvs, minus_itvs, a, b, num_itv, minus_num_itv, end_time)
		cons2 = self.union_itv(minus_itvs, F_itvs, minus_num_itv, new_num_itv, end_time)

		cons = And([cons1, cons2])

		return cons


	########################## Operator G ##########################
	def G_itv(self, itvs, G_itvs, a, b, num_itv, new_num_itv, end_time):


		#ensuring interval bounds are from itvs
		neg_itvs = {i:(Real('neg_itv_%d_0'%i), Real('neg_itv_%d_1'%i)) for i in range(len(itvs))}
		neg_num_itv = Int('neg_num_itv')
		
		cons1 = self.not_itv(itvs, neg_itvs, num_itv, neg_num_itv, end_time)

		F_itvs = {i:(Real('F_itv_%d_0'%i), Real('F_itv_%d_1'%i)) for i in range(len(itvs))}
		F_num_itv = Int('F_num_itv')

		cons2 = self.F_itv(neg_itvs, F_itvs, a, b, neg_num_itv, F_num_itv, end_time)
		cons3 = self.not_itv(F_itvs, G_itvs, F_num_itv, new_num_itv, end_time)

		cons4 = And([self.ensureProperIntervals(neg_itvs, end_time), \
			self.ensureProperIntervals(F_itvs, end_time)])


		cons = And([cons1, cons2, cons3, cons4])

		return cons



# positive interval [4,7], U [1,2]; phi_2 - [a,b] = [2,6], phi_1 [1,5]; 1 U[a,b] 2 = [2,4]
		
	def checking(self):

		#actual_itv1 = [(0,6),(11,12),(16,17),(20,20)]
		#actual_itv1 = [(0,6),(8,12),(16,17),(20,20)]
		#actual_itv1 = [(0, 1),(3, 5),(5, 5),(5, 5),(5, 5),(5, 5),(5, 5),(5, 5),(5, 5),(5, 5),(5, 5),(5, 5)]
		#actual_itv1 = [(2, 7),(8, 19),(20, 20),(20, 20)]
		actual_itv1 = [(5,5),(5,5),(5,5),(5,5),(5,5),(5,5),(5,5),(5,5)]
		actual_itv2 = [(1,4),(11,15),(18,20),(20,20)]

		#[(13,14), (15.1,15.6), (7,15), (16,20)]
		#[(0,17), (20,20)]

		itv1 = {i:(Real('itv1_%d_0'%i), Real('itv1_%d_1'%i)) for i in range(len(actual_itv1))}
		itv2 = {i:(Real('itv2_%d_0'%i), Real('itv2_%d_1'%i)) for i in range(len(actual_itv2))}
		
		itv_new = {i:(Real('itv_new_%d_0'%i), Real('itv_new_%d_1'%i)) for i in range(len(actual_itv1))}

		num_itv1 = Int('num_itv_1')
		num_itv2 = Int('num_itv_2')
		a = Real('a')
		b = Real('b')
		new_num_itv = Int('new_num_itv')

		
		self.solver.add(And([And(itv1[i][0]==actual_itv1[i][0], itv1[i][1]==actual_itv1[i][1]) for i in range(len(actual_itv1))]+[num_itv1==0, a==3, b==4]))
		self.solver.add(And([And(itv2[i][0]==actual_itv2[i][0], itv2[i][1]==actual_itv2[i][1]) for i in range(len(actual_itv2))]+[num_itv2==3]))

		self.solver.add(self.ensureProperIntervals(itv_new, 5))
		#self.solver.add(self.or_itv(itv1, itv2, itv_new, num_itv1, num_itv2, new_num_itv, 20))
		self.solver.add(self.F_itv(itv1, itv_new, a, b, num_itv1, new_num_itv, 5))
		#self.solver.add(self.and_itv(itv1, itv2, itv_new, num_itv1, num_itv2, new_num_itv, 20))

		#self.solver.add(self.not_itv(itv2, itv_new, num_itv2, new_num_itv, 20))
		#print(self.and_itv(itv1, itv2, itv_new, num_itv1, num_itv2, new_num_itv, 20))
		
		solverRes = self.solver.check()
		print(solverRes)

		if solverRes == sat:
			solverModel = self.solver.model()
			for i in range(len(actual_itv1)):
				print(i, (solverModel[itv_new[i][0]],solverModel[itv_new[i][1]]))
			#	print(i, solverModel[self.neg_itvs1[i][0]],solverModel[self.neg_itvs1[i][1]])
			print(solverModel[new_num_itv], solverModel[num_itv1])
			#print(solverModel[self.neg_num_itvs1])	




	def constraints_for_F(self):
		
		#[0,6,7,10, 11, 12, 20,20,20]

		interval_bound = And(1<self.num_tp, self.num_tp<=self.max_intervals)
		self.solver.assert_and_track(interval_bound, 'Bound for number of relevant time points')

		end_point_bound = And([Implies(i>=self.num_tp, self.t[i] == self.end_time) \
								for i in range(1,self.max_intervals+1)])
		self.solver.assert_and_track(end_point_bound, 'End time points')

		
		cons1 = And([Or([Implies(2*i<=self.num_tp,self.t[2*i] == self.s1[2*j]) \
						for j in range(1, even_range+1)]) \
						for i in range(1, even_range+1)])
		self.solver.assert_and_track(cons1, 'Even variables are set to one of the even dummy variables')

		cons2 = And([Or([Implies(2*i-1<=self.num_tp, self.t[2*i-1] == self.s1[2*j-1]) \
						for j in range(1, odd_range+1)]) \
						for i in range(1, odd_range+1)])
		self.solver.assert_and_track(cons2 , 'Odd variables are set to one of the odd dummy variables')
		
		#cons = And([Or([self.t[i] == self.s1[j] \
		#				for j in range(1, self.max_intervals+1)]) \
		#				for i in range(1, self.max_intervals+1)])
		#self.solver.assert_and_track(cons , 'Actual variables are set to one of the dummy variables')

		cons3 = And([Implies(i<self.num_tp, self.t[i]<self.t[i+1]) \
						for i in range(1,self.max_intervals)])
		self.solver.assert_and_track(cons3 , 'Maintain order between variables')	
		
		cons4 = And([Or([And(self.t[2*j-1]<=self.s1[2*i-1], self.s1[2*i]<=self.t[2*j]) \
							for j in range(1, even_range+1)]) \
							for i in range(1, even_range+1)])
		self.solver.assert_and_track(cons4 , 'All intervals must be included')


		cons5 = And([Implies(self.s1[2*i]<self.s1[2*j-1], \
					Implies(And([Or((self.s1[2*i]+self.s1[2*j-1])/2<self.s1[2*k-1], (self.s1[2*i]+self.s1[2*j-1])/2>self.s1[2*k]) \
						for k in range(1, even_range)]),\
						And([Or((self.s1[2*i]+self.s1[2*j-1])/2<self.t[2*l-1], (self.s1[2*i]+self.s1[2*j-1])/2>self.t[2*l]) for l in range(1,even_range)])
						))\
					for i in range(1, even_range+1) for j in range(1, odd_range+1)])
		self.solver.assert_and_track(cons5 , 'No extra variables should be included')

		
	def constraints_for_or_old(self):

		interval_bound = And(1<self.num_tp, self.num_tp<=self.max_intervals)
		self.solver.assert_and_track(interval_bound, 'Bound for number of relevant time points')

		end_point_bound = And([Implies(i>=self.num_tp, self.t[i] == self.end_time) \
								for i in range(1,self.max_intervals+1)])
		self.solver.assert_and_track(end_point_bound, 'End time points')
		
		cons1 = And([Or([Implies(2*i<=self.num_tp,Or(self.t[2*i] == self.s1[2*j], self.t[2*i] == self.s2[2*j])) \
						for j in range(1, self.even_range+1)]) \
						for i in range(1, self.even_range+1)])
		self.solver.assert_and_track(cons1, 'Even variables are set to one of the even dummy variables')

		cons2 = And([Or([Implies(2*i-1<=self.num_tp, Or(self.t[2*i-1] == self.s1[2*j-1], self.t[2*i-1] == self.s2[2*j-1])) \
						for j in range(1, self.odd_range+1)]) \
						for i in range(1, self.odd_range+1)])
		self.solver.assert_and_track(cons2 , 'Odd variables are set to one of the odd dummy variables')

		
		cons3 = And([Implies(i<self.num_tp, self.t[i]<self.t[i+1]) \
						for i in range(1,self.max_intervals)])
		self.solver.assert_and_track(cons3, 'Maintain order between variables')
		
		
		cons4 = And([Implies((self.t[2*i-1]==self.s1[2*j-1]), \
						And([Or(self.s1[2*j-1]<=self.s2[2*k-1], self.s2[2*k]<=self.s1[2*j-1]) for k in range(1, self.even_range+1)]))
						for j in range(1, self.odd_range+1) for i in range(1, self.odd_range+1)])
		self.solver.assert_and_track(cons4, 'Odd variables should be correct for s1 variables')

		cons5 = And([Implies((self.t[2*i]==self.s1[2*j]), \
						And([Or(self.s1[2*j]<=self.s2[2*k-1], self.s2[2*k]<=self.s1[2*j]) for k in range(1, self.even_range+1)]))
						for j in range(1, self.even_range+1) for i in range(1, self.even_range+1)])
		self.solver.assert_and_track(cons5, 'Even variables should be correct for s1 variables')

		print(self.odd_range, self.even_range)
		cons6 = And([Implies((self.t[2*i-1]==self.s2[2*j-1]), \
						And([Or(self.s2[2*j-1]<=self.s1[2*k-1], self.s1[2*k]<=self.s2[2*j-1]) for k in range(1, self.even_range+1)]))
						for j in range(1, self.odd_range+1) for i in range(1, self.odd_range+1)])
		self.solver.assert_and_track(cons6, 'Odd variables should be correct for s2 variables')

		cons7 = And([Implies((self.t[2*i]==self.s2[2*j]), \
						And([Or(self.s2[2*j]<=self.s1[2*k-1], self.s1[2*k]<=self.s2[2*j]) for k in range(1, self.even_range+1)]))
						for j in range(1, self.even_range+1) for i in range(1, self.even_range+1)])
		self.solver.assert_and_track(cons7, 'Even variables should be correct for s2 variables')


	def constraints_for_or(self):

		interval_bound = And(1<self.num_tp, self.num_tp<=self.max_intervals)
		self.solver.assert_and_track(interval_bound, 'Bound for number of relevant time points')

		end_point_bound = And([Implies(i>=self.num_tp, self.t[i] == self.end_time) \
								for i in range(1,self.max_intervals+1)])
		self.solver.assert_and_track(end_point_bound, 'End time points')
		
		cons1 = And([Or([Implies(i<=self.num_tp,Or(self.t[i] == self.s1[j], self.t[i] == self.s2[j])) \
						for j in range(2, self.max_intervals+1, 2)]) \
						for i in range(2, self.max_intervals+1, 2)])
		self.solver.assert_and_track(cons1, 'Even variables are set to one of the even dummy variables')

		cons2 = And([Or([Implies(2*i-1<=self.num_tp, Or(self.t[2*i-1] == self.s1[2*j-1], self.t[2*i-1] == self.s2[2*j-1])) \
						for j in range(1, self.odd_range+1)]) \
						for i in range(1, self.odd_range+1)])
		self.solver.assert_and_track(cons2 , 'Odd variables are set to one of the odd dummy variables')

		
		cons3 = And([Implies(i<self.num_tp, self.t[i]<self.t[i+1]) \
						for i in range(1,self.max_intervals)])
		self.solver.assert_and_track(cons3 , 'Maintain order between variables')
		
		
		cons4 = And([Implies((self.t[2*i-1]==self.s1[2*j-1]), \
						And([Or(self.s1[2*j-1]<=self.s2[2*k-1], self.s2[2*k]<=self.s1[2*j-1]) for k in range(1, self.even_range+1)]))
						for j in range(1, self.odd_range+1) for i in range(1, self.odd_range+1)])
		self.solver.assert_and_track(cons4, 'Odd variables should be correct for s1 variables')

		cons5 = And([Implies((self.t[2*i]==self.s1[2*j]), \
						And([Or(self.s1[2*j]<=self.s2[2*k-1], self.s2[2*k]<=self.s1[2*j]) for k in range(1, self.even_range+1)]))
						for j in range(1, self.even_range+1) for i in range(1, self.even_range+1)])
		self.solver.assert_and_track(cons5, 'Even variables should be correct for s1 variables')

		print(self.odd_range, self.even_range)
		cons6 = And([Implies((self.t[2*i-1]==self.s2[2*j-1]), \
						And([Or(self.s2[2*j-1]<=self.s1[2*k-1], self.s1[2*k]<=self.s2[2*j-1]) for k in range(1, self.even_range+1)]))
						for j in range(1, self.odd_range+1) for i in range(1, self.odd_range+1)])
		self.solver.assert_and_track(cons6, 'Odd variables should be correct for s2 variables')

		cons7 = And([Implies((self.t[2*i]==self.s2[2*j]), \
						And([Or(self.s2[2*j]<=self.s1[2*k-1], self.s1[2*k]<=self.s2[2*j]) for k in range(1, self.even_range+1)]))
						for j in range(1, self.even_range+1) for i in range(1, self.even_range+1)])
		self.solver.assert_and_track(cons7, 'Even variables should be correct for s2 variables')

'''

'''
def minus_itv(itvs, minus_itvs, a, b, num_itv, new_num_itv, end_time):

	cons1 = And([Implies(i<new_num_itv,\
		Or([And([j<num_itv, \
			minus_itvs[i][0]==If(itvs[j][0]-b>0, itvs[j][0]-b, 0), minus_itvs[i][1]==If(itvs[j][1]>a, itvs[j][1]-a, 0)]) \
			for j in range(len(itvs))])) for i in range(len(itvs))])

	cons2 = And([Implies(And([i<num_itv]+[itvs[i][1]-a != minus_itvs[j][1] for j in range(len(itvs))]),\
						itvs[i][1] <= a)
						for i in range(len(itvs))])

	cons3 = And([minus_itvs[i][1]>0 for i in range(len(itvs))])

	cons4 = And([And(minus_itvs[i-1][0]<=minus_itvs[i][0], minus_itvs[i-1][1]<=minus_itvs[i][1])\
									 for i in range(1,len(itvs))]) 

	cons5 = And([Implies(i >= new_num_itv, \
				And(minus_itvs[i][0]==end_time, minus_itvs[i][1]==end_time)) for i in range(len(itvs))])

	cons = And([cons1, cons2, cons3, cons4, cons5])

	return cons
'''
