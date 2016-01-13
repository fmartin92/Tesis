def n_slices(n, list_):
    for i in xrange(len(list_) + 1 - n):
        yield list_[i:i+n]

def is_sublist(list_, sub_list):
    for slice_ in n_slices(len(sub_list), list_):
        if slice_ == sub_list:
            return True
    return False
    
def grlex_sort(list_):
    return sorted(sorted(list_), key=len)

class Term:
    def __init__(self, body, sign):
        self.body = body
        self.sign = sign
        
    def __eq__(self, other):
        if self.body == ():
            return (self.body == other.body)
        else:
            return (self.body == other.body) and (self.sign == other.sign)
            
    def __repr__(self):
        if self.sign == -1:
            return '-' + str(self.body)
        else:
            return str(self.body)
  
    def __len__(self):
        return len(self.body)

class Rewriting_System:
    def __init__(self, triangulation, zero_rules_flag=False):
        self.triangulation = triangulation
        self.generate_qp()
        self.ambiguity_depth = 20
        self.zero_depth = 50
        self.rules = {}
        self.zero_rules_flag = zero_rules_flag
        self.rewriting_rules()
        
    def generate_qp(self):
        dict = {}
        edges = self.triangulation.edges(labels=False)
        faces = [map(tuple, map(sorted, face)) for face in self.triangulation.faces()]
        
        for i, edge in enumerate(edges):
            key = []
            for face in faces:
                if edge in face:
                    ind = face.index(edge)            
                    if ind == len(face)-1:
                        key.append(edges.index(face[0]))
                    else:
                        key.append(edges.index(face[ind+1]))
            dict[i] = key  
        
        self.quiver = DiGraph(dict)
        self.potential = []
        
        #cycles from faces
        for face in faces:
            self.potential.append(map(edges.index, face + [face[0]]))
        
        #cycles from punctures
        for puncture in self.triangulation:
            unordered_cycle = map(edges.index, self.triangulation.edges_incident(puncture, labels=False))
            cycle = [unordered_cycle[0]]
            for _ in xrange(len(unordered_cycle)):
                cycle.append([vertex for vertex in dict[cycle[-1]] if vertex in unordered_cycle][0])
            self.potential.append(cycle)
       
    def cyclic_derivative(self, edge):
        derivative = []
        for cycle in self.potential:
            if is_sublist(cycle, edge):
                if edge[1] == cycle[0]:
                    derivative.append(cycle[:-1])
                else:
                    i = cycle.index(edge[1])
                    derivative.append(cycle[i:] + cycle[1:i])
        return grlex_sort(derivative)
    
    def reduce(self, term):
        term_length = len(term)
        body = term.body
        for i in xrange(0, term_length):
            for j in self.rules.keys():
                rule_length = len(j)
                if (term_length - i >= rule_length) and body[i:i+rule_length] == j:
                    rep = self.rules[j]
                    if rep:
                        return Term(body[:i] + rep.body + body[i+rule_length:], rep.sign * term.sign)
                    else:
                        return Term((), 1)
        return term
                
    def n_paths(self, n):
        return [path for path in self.quiver.all_paths_iterator(max_length=n+1, trivial=True) if len(path)==n+1]
    
    def is_zero(self, term):
        for _ in xrange(2*self.zero_depth):
            next_term = self.reduce(term)
            if next_term == term:
                break
            term = next_term
        return (len(next_term) > self.zero_depth) or (len(next_term) == 0)
            
    def null_n_paths(self, n):
        return [tuple(path) for path in self.n_paths(n) if self.is_zero(Term(tuple(path), 1))]
        
    def ambiguities(self):
        forbidden_terms = self.rules.keys()
        length = max(map(len, forbidden_terms))-1
        ambs = []
        for n in xrange(1,length):
            for x in forbidden_terms:
                for y in forbidden_terms:
                    if x != y and x[-n-1:] == y[:n+1]:
                        ambs.append([x, y, x + y[n+1:]])
        return ambs
    
    def is_unsolvable(self, amb):
        rule0 = self.rules[amb[0]]
        rule1 = self.rules[amb[1]]
        if rule0.body == ():
            leaf0 = Term((), 1)
        else:
            leaf0 = Term(rule0.body + amb[2][len(amb[0]):], rule0.sign)
        if rule1.body == ():
            leaf1 = Term((), 1)
        else:
            leaf1 = Term(amb[2][:-len(amb[1])] + rule1.body, rule1.sign)   

        for _ in xrange(self.ambiguity_depth):
            leaf0 = self.reduce(leaf0)
            leaf1 = self.reduce(leaf1)
            if leaf0 == leaf1:
                return False
            
        if leaf0.body == ():
            return [leaf1.body, Term((), 1)]
        elif leaf1.body == ():
            return [leaf0.body, Term((), 1)]
        elif (leaf0.body == leaf1.body) and (leaf0.sign != leaf1.sign):
            return [leaf0.body, Term((), 1)]
        else:
            r1, r2 = grlex_sort([leaf0.body] + [leaf1.body])
            return [r1, Term(r2, leaf0.sign * leaf1.sign)]
        
        
    def needed_rules(self):
        new_rules = {}
        for amb in self.ambiguities():
            new_rule_needed = self.is_unsolvable(amb)
            if new_rule_needed:
                new_rules[new_rule_needed[0]] = new_rule_needed[1]
        return new_rules
        
    def rewriting_rules(self):
        for vertex in self.quiver.vertices():
            for neighbor in self.quiver.neighbor_out_iterator(vertex):
                derivative = self.cyclic_derivative([vertex,neighbor])
                self.rules[tuple(derivative[0])] = Term(tuple(derivative[1]), -1)
        if self.zero_rules_flag:
            zero_paths = []
            n = 3
            while not zero_paths:
                zero_paths = self.null_n_paths(n)
                n += 1
            self.rules.update(dict.fromkeys(zero_paths, Term((), 1)))
        
        missing_rules = self.needed_rules()
        while missing_rules:
            self.rules.update(missing_rules)
            print len(missing_rules), 'rules added.'
            missing_rules = self.needed_rules()
        self.rules.update(missing_rules)
        print 'Total rules:', len(self.rules)
    
    def is_admissible(self, path):
        for forbidden in self.rules.keys():
            if is_sublist(path, list(forbidden)):
                return False
        return True
    
    def basis(self, max_degree):
        homogeneous_bases = [self.n_paths(n) for n in xrange(2)]
        for _ in xrange(2, max_degree):
            cur_degree_paths = []
            for j in homogeneous_bases[-1]:
                cur_degree_paths += [[k]+j for k in self.quiver.neighbor_in_iterator(j[0])]
            admissible_paths = filter(lambda path: self.is_admissible(path), cur_degree_paths)
            homogeneous_bases.append(sorted(admissible_paths))
        return homogeneous_bases
               
    def irred_paths(self, max_degree):
        return map(len, self.basis(max_degree))