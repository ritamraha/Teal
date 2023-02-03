def compute_prop_intervals(signal, props, prop2num, end_time):

	timepoints = [sp.time for sp in signal.sequence]
	prop_itvs = {}
	max_prop_intervals=0
	itv = ()
	for p in props:	
		parity = 0
		itvs = []
		for sp in signal.sequence:
			if parity == 0 and sp.vector[prop2num[p]] == 1:
				parity = 1
				itv = (sp.time,)
				continue

			if parity == 1 and sp.vector[prop2num[p]] == 0:
				parity = 0
				itv += (sp.time,)
				itvs.append(itv)
				itv = ()
				continue

		if len(itv) == 1:
			itv += (end_time,)
			itvs.append(itv)
		prop_itvs[p] = itvs
		max_prop_intervals = max(max_prop_intervals, len(itvs))

	return prop_itvs


def check_consistency_G(formula, signal_sample):

		props = signal_sample.propositions
		prop2num = {props[i]:i for i in range(len(props))}
		end_time = signal_sample.end_time
		for signal in signal_sample.positive:
			prop_itvs = compute_prop_intervals(signal, props, prop2num, end_time)
			if not sat_check_G(prop_itvs, formula, end_time):
				print('Formula is wrong!!!')
				return False

		for signal in signal_sample.negative:
			prop_itvs = compute_prop_intervals(signal, props, prop2num, end_time)
			if sat_check_G(prop_itvs, formula, end_time):
				print(signal)
				print(prop_itvs)
				print('Formula is wrong!!!')
				return False
		
		print('Formula is correct')
		return True


def sat_check(prop_itvs, formula, end_time):

	pos_itvs = monitor(prop_itvs, formula, end_time)
	#print(pos_itvs)
	if pos_itvs!=[] and pos_itvs[0][0]==0:
		return True
	else:
		return False

def sat_check_G(prop_itvs, formula, end_time):

	pos_itvs = monitor(prop_itvs, formula, end_time)
	#print(pos_itvs)
	if pos_itvs!=[] and pos_itvs[0][0]==0 and pos_itvs[0][1]==end_time:
		return True
	else:
		return False


def monitor(prop_itvs, formula, end_time):

	props = list(prop_itvs.keys())
	label = formula.label
	left = formula.left
	right = formula.right
	time_interval= formula.time_interval
	#print(label)

	if label=='|':
		
		return compute_or_itvs(monitor(prop_itvs, left, end_time), \
								monitor(prop_itvs,right, end_time), end_time)
		
	if label=='&':
		return compute_and_itvs(monitor(prop_itvs, left, end_time), \
								monitor(prop_itvs,right, end_time), end_time)

	if label=='!':
		return compute_not_itvs(monitor(prop_itvs, left, end_time), end_time)
		
	
	if label=='F':
		try:
			lb_frac = time_interval[0].as_fraction()
			ub_frac = time_interval[1].as_fraction()
			a = float(lb_frac.numerator)/float(lb_frac.denominator)
			b = float(ub_frac.numerator)/float(ub_frac.denominator)
		except:
			a = time_interval[0]
			b = time_interval[1]
		return compute_F_itvs(monitor(prop_itvs, left, end_time),a, b, end_time)
		
	
	if label=='G':
		try:
			lb_frac = time_interval[0].as_fraction()
			ub_frac = time_interval[1].as_fraction()
			a = float(lb_frac.numerator)/float(lb_frac.denominator)
			b = float(ub_frac.numerator)/float(ub_frac.denominator)
		except: 
			a = time_interval[0]
			b = time_interval[1]
		return compute_G_itvs(monitor(prop_itvs, left, end_time),a, b, end_time)	
	
	if label in props:
		return prop_itvs[label]


def compute_F_itvs(itvs, a, b, end_time):

	if itvs == []:
		return []

	#print(type(itvs[0][0]),type(a))
	minus_itvs_og = [(max(itvs[i][0]-b,0),max(itvs[i][1]-a,0)) for i in range(len(itvs))]
	
	if a !=0:
		minus_itvs_og.append([max(end_time-a,0), end_time])

	#removing (0,0) itvs
	minus_itvs = [(i,j) for (i,j) in minus_itvs_og if j!=0]
	if minus_itvs == []:
		return []

	union_itvs = []
	current_itv = minus_itvs[0]
	len_minus_itv = len(minus_itvs) 
	head = 0
	while True:

		head+=1
		if head==len_minus_itv:
			union_itvs.append(current_itv)
			break

		if minus_itvs[head][0] <= current_itv[1] and current_itv[1] <= minus_itvs[head][1]:
			current_itv = (current_itv[0],minus_itvs[head][1])
		elif minus_itvs[head][1] < current_itv[1]:
			continue
		else:
			union_itvs.append(current_itv)
			current_itv = minus_itvs[head]

	return union_itvs

def compute_G_itvs(itvs, a, b, end_time):

	not_itvs = compute_not_itvs(itvs, end_time)
	F_itvs = compute_F_itvs(not_itvs, a, b, end_time)
	G_itvs = compute_not_itvs(F_itvs, end_time)

	if G_itvs == []:
		return [(end_time-a, end_time)]

	if G_itvs[-1][1] >= end_time-a:
		G_itvs[-1] = (G_itvs[-1][0],end_time)
	else:
		G_itvs.append((end_time-a, end_time))

	return G_itvs

def compute_or_itvs(itvs1, itvs2, end_time):
	
	if itvs1 == []:
		return itvs2
	if itvs2 == []:
		return itvs1

	union_itvs = itvs1+itvs2	
	union_itvs.sort()

	return compute_F_itvs(union_itvs, 0, 0, end_time)



def compute_and_itvs(itvs1, itvs2, end_time):
	
	not_itvs1 = compute_not_itvs(itvs1, end_time)
	not_itvs2 = compute_not_itvs(itvs2, end_time)
	or_itvs = compute_or_itvs(not_itvs1, not_itvs2, end_time)

	return compute_not_itvs(or_itvs, end_time)
	

def compute_not_itvs(itvs, end_time):
	
	if itvs == []:
		return [(0,end_time)]
	

	not_itvs = [(itvs[i][1], itvs[i+1][0]) for i in range(len(itvs)-1)]

	if itvs[0][0] != 0:
		not_itvs.insert(0, (0,itvs[0][0]))
	if itvs[-1][1] != end_time:
		not_itvs.append((itvs[-1][1], end_time))

	return not_itvs


#print(compute_G_itvs([(1,5)],1, 2, 10))
#print(compute_F_itvs([(0,1), (2,6)],0,1,7))
