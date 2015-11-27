def n_slices(n, list_):
  for i in xrange(len(list_) + 1 - n):
    yield list_[i:i+n]

def is_sublist(list_, sub_list):
  for slice_ in n_slices(len(sub_list), list_):
    if slice_ == sub_list:
      return True
  return False

class Rewriting_System:
  def __init__(self, *args):
    if len(args) == 1 and type(args[0]) == Graph:
      self.triangulation = args[0]
      self.generate_qp()
    if len(args) == 2 and type(args[0]) == DiGraph and type(args[1]) == list:
      self.quiver, self.potential = args[0], args[1]
    self.checked_rules = {}
    self.unchecked_rules = {}
    self.all_rules = {}
    self.zero_depth = 30
    self.ambiguity_depth = 30
    self.add_zero_rules = False
    self.rewriting_rules()
    
  def generate_qp(self):
    dict = {}
    faces = self.triangulation.faces()
    for edge in self.triangulation.edges(labels=False):
      value = []
      for face in faces:
        sorted_face = map(tuple, map(sorted, face)) #the edge (x,y) may be represented as (y,x) in the face...
        if edge in sorted_face: 
          value.append((sorted_face*2)[sorted_face.index(edge)+1])
      dict[edge] = value
    
    potential = []
    
    #cycles from faces
    for face in faces:
      sorted_face = map(sorted, face)
      potential.append(map(tuple, sorted_face + [sorted_face[0]]))
    
    #cycles from punctures
    for puncture in self.triangulation:
      cycle = self.triangulation.edges_incident(puncture, labels=False) #may not be in the correct order
      correct_cycle = [cycle[0]]
      for _ in range(len(cycle)):
        correct_cycle.append([vertex for vertex in dict[correct_cycle[-1]] if vertex in cycle][0])
      potential.append(correct_cycle)
    
    new_dict = {}
    old_keys = dict.keys()
    for i, vertex in enumerate(old_keys):
      new_dict[i] = map(lambda j: old_keys.index(j), dict[vertex])
    self.quiver = DiGraph(new_dict)
    self.potential = [map(lambda j: old_keys.index(j), cycle) for cycle in potential]
  
  def cyclic_derivative(self, edge):
    derivative = []
    for cycle in self.potential:
      aux = cycle[1:]
      for _ in range(len(cycle)-1):
        if (edge[1] == aux[0]) and (edge[0] == aux[-1]):
          derivative.append(aux)
        aux = aux[1:] + [aux[0]]
    return sorted(sorted(derivative), key=len) #gr-lex :)
  
  def ambiguities(self):
    checked_forbidden_terms = self.checked_rules.keys()
    unchecked_forbidden_terms = self.unchecked_rules.keys()
    
    length = max(map(len, checked_forbidden_terms + unchecked_forbidden_terms))-1
    ambs = []
    
    #for n in range(1,length):
    #  for x in checked_forbidden_terms:
    #    for y in checked_forbidden_terms:
    #      if x != y and x[-n-1:] == y[:n+1]:
    #        ambs.append(map(list, [x, y, x + y[n+1:]]))
            
    #checked vs unchecked
    for n in range(1,length):
      for x in checked_forbidden_terms:
        for y in unchecked_forbidden_terms:
          if x != y and x[-n-1:] == y[:n+1]:
            ambs.append(map(list, [x, y, x + y[n+1:]]))
            
    #unchecked vs checked
    for n in range(1,length):
      for x in unchecked_forbidden_terms:
        for y in checked_forbidden_terms:
          if x != y and x[-n-1:] == y[:n+1]:
            ambs.append(map(list, [x, y, x + y[n+1:]]))
            
    #unchecked vs unchecked
    length = max(map(len, unchecked_forbidden_terms))-1
    for n in range(1,length):
      for x in unchecked_forbidden_terms:
        for y in unchecked_forbidden_terms:
          if x != y and x[-n-1:] == y[:n+1]:
            ambs.append(map(list, [x, y, x + y[n+1:]]))
    return ambs
  
  def reduce(self, term):
    term_length = len(term[0])
    for i in range(0, term_length):
      for j in self.all_rules.keys():
        rule_length = len(j)
        if (term_length - i >= rule_length) and term[0][i:i+rule_length] == j:
          if self.all_rules[j][0]:
            return [term[0][:i] + tuple(self.all_rules[term[0][i:i+rule_length]][0]) + term[0][i+rule_length:], term[1] == self.all_rules[j][1]]
          else:
            return [(), True]
    return term
    
  def is_zero(self, term):
    cur_term = term
    for _ in xrange(2*self.zero_depth): #adjust reasonably
      next_term = self.reduce(cur_term)
      if next_term == cur_term:
        break
      cur_term = next_term
    return (len(next_term[0]) > self.zero_depth) or (next_term[0] == ())
  
  def all_n_paths(self, n):
    return [path for path in self.quiver.all_paths_iterator(max_length=n+1, trivial=True) if len(path) == n+1]

  def all_null_n_paths(self, n):
    return [tuple(path) for path in self.all_n_paths(n) if self.is_zero([tuple(path), True])]
  
  def is_unsolvable(self, amb):
    if self.all_rules[tuple(amb[0])][0] == (): leaf1 = [(), True]
    else: leaf1 = [tuple(self.all_rules[tuple(amb[0])][0]) + tuple(amb[2][len(amb[0]):]), self.all_rules[tuple(amb[0])][1]]
    if self.all_rules[tuple(amb[1])][0] == (): leaf2 = [(), True]
    else: leaf2 = [tuple(amb[2][:-len(amb[1])]) + tuple(self.all_rules[tuple(amb[1])][0]), self.all_rules[tuple(amb[1])][1]]
    
    if amb == [[3, 1, 2, 15, 7, 12, 4, 10, 11], [10, 11, 4], [3, 1, 2, 15, 7, 12, 4, 10, 11, 4]]:
        print leaf1, leaf2
        
    for _ in xrange(self.ambiguity_depth):
      leaf1 = self.reduce(leaf1)
      leaf2 = self.reduce(leaf2)
      if amb == [[3, 1, 2, 15, 7, 12, 4, 10, 11], [10, 11, 4], [3, 1, 2, 15, 7, 12, 4, 10, 11, 4]]:
        print leaf1, leaf2
      if leaf1 == leaf2:
        return False

    
    if leaf1[0] == () or leaf1[0] == leaf2[0]:
      return [leaf2[0], (), True]
    elif leaf2[0] == ():
      return [leaf1[0], (), True]
    else:
      n_rule = sorted(sorted([leaf1[0], leaf2[0]]), key=len)
      n_rule.append(leaf1[1] == leaf2[1])
      return n_rule
  
  def new_rules(self):
    ambs = self.ambiguities()
    #for i in ambs: print i
    #print ambs[-1]
    n_rules = {}
    for amb in ambs:
      new_rule_needed = self.is_unsolvable(amb)
      if new_rule_needed:
        n_rules[new_rule_needed[0]] = new_rule_needed[1:]
        #print new_rule_needed
    return n_rules
  
  def rewriting_rules(self):
    if not self.checked_rules:
      for vertex in range(len(self.quiver)):
        for neighbor in self.quiver.neighbor_out_iterator(vertex):
          derivative = self.cyclic_derivative([vertex, neighbor])
          self.unchecked_rules[tuple(derivative[0])] = [tuple(derivative[1]), False]
      self.all_rules = self.unchecked_rules.copy()
      if self.add_zero_rules:
        zero_paths = []
        n = 3
        while zero_paths == []:
          zero_paths = self.all_null_n_paths(n)
          n += 1
        self.unchecked_rules.update(dict.fromkeys(zero_paths, [(), True]))
      self.all_rules = self.unchecked_rules.copy()
      
      #print self.all_rules
      missing = self.new_rules()
      while missing:
        self.checked_rules.update(self.unchecked_rules)
        self.unchecked_rules = missing
        self.all_rules.update(missing)
        print len(missing), 'rules added.'
        missing = self.new_rules()
      self.checked_rules.update(self.unchecked_rules)
      print 'Total rules:', len(self.checked_rules)
    return self.checked_rules
     
  def is_admissible(self, term):
    for forbidden in self.all_rules.keys():
      if is_sublist(term, list(forbidden)):
        return False
    return True
  
  def basis(self, max_degree):
    homogeneous_bases = [self.all_n_paths(n) for n in range(2)]
    for _ in range(2, max_degree):
      cur_degree_paths = []
      for j in homogeneous_bases[-1]:
        cur_degree_paths += [[k]+j for k in self.quiver.neighbor_in_iterator(j[0])]
      admissible_paths = filter(lambda term: self.is_admissible(term), cur_degree_paths)
      homogeneous_bases.append(sorted(admissible_paths))
    return homogeneous_bases
    
  def hilbert_series(self, max_degree):
    return map(len, self.basis(max_degree)):