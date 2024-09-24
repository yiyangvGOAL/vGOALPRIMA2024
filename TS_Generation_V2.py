import copy
import time


keywords = ["forall", "exists", "not", "and", "implies", "or", "pre", "post", "a-goal", "=", "bel",
            "goal", "allgoals", "True", "False", "send:", "send!", "send?", "sent:", "sent!", "sent?","adopt", "drop", "insert", "delete", "allother",
            "all","insert"]
Event_Keywords=["adopt", "drop", "insert", "delete"]
Communication_Keywords=["send:", "send!", "send?", "sent:", "sent!", "sent?"]
symbols = ["(", ")", ".", ",", "[", "]", "|"]

class Agent:
    def __init__(self, name, belief_base, goals):
        self.name = name
        self.belief_base = belief_base
        self.goals = goals
        self.last_beliefs=[]
        self.decision_needed=False
        self.sent_messages = []
        self.received_messages = []
        self.desired_next_state = []

# Retrieve all information from the predicate, the input predicate is contained in a string,
# the output of all information of the predicate are stored in a standard form.
def predicate_information(predicate,constants):
    information = {"name": "", "list_contain": "", "values_in_list": [[], []], "values_in_non_list": [],
                   "variables": []}
    i = 0
    flag = 0
    empty = True
    evaluated = False
    name = ""
    nested = False
    while i < len(predicate):
        if flag == 0 and predicate[i] != '(':
            information["name"] = information["name"] + predicate[i]
        elif flag == 0 and predicate[i] == '(':
            flag = 1
        elif flag == 1 and predicate[i] == '[':
            information["list_contain"] = True
            flag = 2
        elif flag == 1 and predicate[i] != '[':
            information["list_contain"] = False
            name = name + predicate[i]
            flag = 3
        # Store list value in two sublist, need one more flag to store if the second list is empty.
        elif flag == 2 and empty:
            if predicate[i] != ',' and predicate[i] != '|' and predicate[i] != ']':
                name = name + predicate[i]
            elif predicate[i] == '|':
                empty = False
                information["values_in_list"][0].append(name)
                if name not in constants:
                    information["variables"].append(name)
                name = ""
            else:
                information["values_in_list"][0].append(name)
                if name not in constants:
                    information["variables"].append(name)
                name = ""
        elif flag == 2 and not empty:
            if not nested and not evaluated:
                evaluated = True
                if predicate[i] != '[':
                    nested = True
            if not nested:
                if predicate[i] != ',' and predicate[i] != '[' and predicate[i] != ']':
                    name = name + predicate[i]
                elif predicate[i] == ',' or predicate[i] == ']':
                    if name != "":
                        information["values_in_list"][1].append(name)
                        if name not in constants:
                            information["variables"].append(name)
                        name = ""
            elif evaluated and nested:
                if predicate[i] != ']':
                    name = name + predicate[i]
                else:
                    information["values_in_list"][1] = name
                    information["variables"].append(name)
        elif flag == 3:
            if predicate[i] != ',' and predicate[i] != ')':
                name = name + predicate[i]
            elif predicate[i] == ',' or predicate[i] == ')':
                if name != "":
                    information["values_in_non_list"].append(name)
                    if name not in constants:
                        information["variables"].append(name)
                    name = ""
        i = i + 1
    return information

# Process a rule of the inputs
def input_process(rule,constants):
    standard_form = []
    for predicate in rule:
        if predicate in keywords:
            standard_form.append(predicate)
        else:
            standard_form.append(predicate_information(predicate,constants))
    return standard_form

#Process a belief base
def process_bliefs(beliefs,constants):
    processed = []
    for i in beliefs:
        processed.append(predicate_information(i,constants))
    return processed

#Process a goal base
def process_belief_list(belief_list,constants):
    processed = []
    for i in belief_list:
        processed.append(process_bliefs(i,constants))
    return processed

# Transform a predicate to a readble form
def transform_to_normalform(predicate_information):
    predicate = predicate_information['name']
    if predicate_information['values_in_list'] == [[], []] and predicate_information['values_in_non_list'] == [] and \
            predicate_information["variables"] == []:
        return predicate
    if predicate_information['list_contain']:
        predicate = predicate + "(["
        pr = predicate_information['values_in_list'][0]
        i = 0
        while i < len(pr):
            predicate = predicate + pr[i]
            if i < len(pr) - 1:
                predicate = predicate + ','
            else:
                predicate = predicate + '])'
            i = i + 1
    else:
        predicate = predicate + "("
        pr = predicate_information['values_in_non_list']
        i = 0
        while i < len(pr):
            predicate = predicate + pr[i]
            if i < len(pr) - 1:
                predicate = predicate + ','
            else:
                predicate = predicate + ')'
            i = i + 1
    return predicate

# Transform a state list to the readable form
def state_normal_representation(state):
    normal = []
    for item in state:
        normal.append(transform_to_normalform(item))
    return normal

#Transform a state list to the readable form
def state_list_normal_representation(states):
    reformed = []
    for state in states:
        reformed.append(state_normal_representation(state))
    return reformed

def system_goals_normal_representation(system_goals):
    goals_rep = {}
    for key in system_goals:
        goals_rep.update({key: state_list_normal_representation(system_goals[key])})
    return goals_rep

#Transform a system state to the readable form
def system_state_normal_representation(system_state):
    reformed = {}
    for key in system_state:
        B = system_state[key][0]
        G = system_state[key][1]
        B2 = state_normal_representation(B)
        G2 = state_list_normal_representation(G)
        reformed.update({key: (B2, G2)})
    return reformed

#Transform multiple system state to the readable form
def transform_multi_states_normal(multi_state):
    reformed=[]
    for key in multi_state:
        B=state_normal_representation(multi_state[key][0])
        G=state_list_normal_representation(multi_state[key][1])
        D={key:(B,G)}
        reformed.append(D)
    return reformed

#Transform a mental state to the readable form.
def transform_mental_states_normal(mental_state):
    B=state_normal_representation(mental_state[0])
    G=state_list_normal_representation(mental_state[1])
    return (B,G)

# Transform a rule to the readable form
def rule_normal_representation(rule, constants):
    normal = ""
    for item in rule:
        if type(item) == type(True):
            item = str(item)
        if (item in keywords and item not in Event_Keywords) or item in constants:
            normal = normal + str(item) + " "
        elif item in Event_Keywords:
            normal=normal+str(item)+ "-"
        elif item['name'] in Communication_Keywords:
            normal = normal + transform_to_normalform(item)  + "-"
        else:
            normal = normal + transform_to_normalform(item) + " "
    return normal

def rules_normal_representation(rules,constants):
    R=[]
    for r in rules:
        R.append(rule_normal_representation(r,constants))
    return R

#Test if a system state is a final state
def test_final_state(state):
    for key in state:
        for key2 in state[key]:
            if state[key][key2][1] != []:
                return False
    return True

# Find the all occurrence positions of the keyword in the list, return a list either contain all occurrence of the keyword in the list.
def find_position_in_list(L, keyword):
    i = 0
    store = []
    while i < len(L):
        if L[i] == keyword:
            store.append(i)
        i = i + 1
    return store

# Evaluate if the given variable occurs at the both side of the implication rule
def variable_implication_both_side(rule, var):
    left = False
    right = False
    for predicate in rule[0:find_position_in_list(rule, "implies")[0]]:
        if predicate not in keywords:
            if var in predicate["variables"]:
                left = True
    for predicate in rule[find_position_in_list(rule, "implies")[0] + 1:]:
        if predicate not in keywords:
            if var in predicate["variables"]:
                right = True
    return left and right

# Remove single universal variables only occuring at the one side of implication
def instantiate_universal_variable_implication_single(rule, var, domain):
    previous_symbol_not = False
    instantiated_rule = []
    not_add = False
    for predicate in rule:
        if predicate not in keywords:
            if var in predicate["variables"]:
                for value in domain:
                    if previous_symbol_not and not_add:
                        instantiated_rule.append("not")
                    predicate_copy = copy.deepcopy(predicate)
                    if predicate_copy["list_contain"]:
                        i = 0
                        while i < len(predicate_copy["values_in_list"][0]):
                            if predicate_copy["values_in_list"][0][i] == var:
                                predicate_copy["values_in_list"][0][i] = value
                                predicate_copy["variables"].remove(var)
                            i = i + 1
                    else:
                        i = 0
                        while i < len(predicate_copy["values_in_non_list"]):
                            if predicate_copy["values_in_non_list"][i] == var:
                                predicate_copy["values_in_non_list"][i] = value
                                predicate_copy["variables"].remove(var)
                            i = i + 1
                    instantiated_rule.append(predicate_copy)
                    instantiated_rule.append("and")
                    not_add = True
            else:
                instantiated_rule.append(predicate)
            if instantiated_rule[-1] == "and":
                instantiated_rule = instantiated_rule[:-1]
            previous_symbol_not = False
        else:
            instantiated_rule.append(predicate)
            if predicate == "not":
                previous_symbol_not = True
            else:
                previous_symbol_not = False
    return instantiated_rule

# Remove all universal variables and remove all quantified parts.
def universal_variable_instantiation(L, domain,constants):
    universal_vars = []
    positions = find_position_in_list(L, 'in')
    var_domain = {}
    for pos in positions:
        var_domain.update({L[pos - 1][-1]: L[pos + 1]})
    if positions != []:
        new_L = []
        i = 0
        while i < len(positions):
            if i == 0:
                new_L = new_L + L[0:positions[i]]
                S = new_L[-1]
                S = S + L[positions[i] + 2]
                new_L[-1] = S
            else:
                new_L = new_L + L[positions[i - 1] + 3:positions[i]]
                S = new_L[-1] + L[positions[i] + 2]
                new_L[-1] = S
            i = i + 1
        new_L = new_L + L[positions[-1] + 3:]
        L = new_L
    if L[0] == "forall":
        for i in L[1]:
            if i != "," and i != ".":
                universal_vars.append(i)
        L = L[2:]
    if L[0] == "exists":
        L = L[2:]
    universal_var_single = []
    universal_var_both = []
    rule = input_process(L,constants)
    for var in universal_vars:
        if variable_implication_both_side(rule, var):
            universal_var_both.append(var)
        else:
            universal_var_single.append(var)
    rules = []
    rules_copy = [copy.deepcopy(rule)]

    if universal_var_single != []:
        for new_rule in rules_copy:
            temp = new_rule

            for var in universal_var_single:
                temp = instantiate_universal_variable_implication_single(temp, var, domain[var_domain[var]])
            rules.append(temp)

        rules = [x for x in rules if x not in rules_copy]
    if universal_var_single == []:
        rules.append(rule)
    return rules

#Separate rules into fully instatiated rules and partial instantiated rules
def separate_rules(L, domain,constants):
    universal_instantiated_rules = []
    for rule in L:
        processed_rules=universal_variable_instantiation(rule, domain,constants)
        processed_rules_copy=copy.deepcopy(processed_rules)
        for i in processed_rules_copy:
            universal_instantiated_rules.append(i)
    fully_instantiated_rules = []
    partial_instantiated_rules = []
    for rule in universal_instantiated_rules:
        fully_instantiated = True
        r = 0
        while r < len(rule) and fully_instantiated:
            if rule[r] not in keywords:
                if rule[r]["variables"] != []:
                    fully_instantiated = False
            r = r + 1
        if fully_instantiated:
            fully_instantiated_rules.append(rule)
        partial_instantiated_rules = [x for x in universal_instantiated_rules if x not in fully_instantiated_rules]
    return (fully_instantiated_rules, partial_instantiated_rules)

def instatiate_rules(L, domain,constants):
    universal_instantiated_rules = []
    for rule in L:
        processed_rules=universal_variable_instantiation(rule, domain,constants)
        processed_rules_copy=copy.deepcopy(processed_rules)
        for i in processed_rules_copy:
            universal_instantiated_rules.append(i)
    return universal_instantiated_rules

# Extract all predicates' name of a rule
def predicate_in_rules(rule):
    predicate_names = []
    for predicate in rule:
        if predicate not in keywords:
            if predicate["name"] not in predicate_names:
                predicate_names.append(predicate["name"])
    return predicate_names

# Return the position of a predicate occuring in the rule: use to evaluate if a predicate
# occurs both of the implication.
def predicate_position_implies(predicate_name, rule):
    i = 0
    place = "Unknown"
    while i < len(rule) and place != "right":
        if rule[i] not in keywords:
            if rule[i]["name"] == predicate_name:
                if 'implies' in rule[i + 1:]:
                    place = "Left"
                elif 'implies' in rule[:i] and place != "Left":
                    place = "Right"
                elif 'implies' in rule[:i]:
                    place = "Both"
        i = i + 1
    return place

# For a set of predicates and rules, return a pair containing the position information of each predicate
def predicates_position_in_rules(predicates, rules):
    predicates_position = []
    for i in predicates:
        j = 0
        flag = True
        position = "Unknown"
        while j < len(rules) and flag:
            if position == "Unknown":
                position = predicate_position_implies(i, rules[j])
            elif position == "Left":
                if predicate_position_implies(i, rules[j]) == "Right" or predicate_position_implies(i,
                                                                                                    rules[j]) == "Both":
                    position = "Both"
                    flag = False
            elif position == "Right":
                if predicate_position_implies(i, rules[j]) == "Left" or predicate_position_implies(i,
                                                                                                   rules[j]) == "Both":
                    position = "Both"
                    flag = False
            j = j + 1
        predicates_position.append((i, position))
    return predicates_position

# In a rule, evaluate if all predicates occuring at the leftside belong to the give predicates set.
# This function is usually used to evaluates if the rule should be instantiated at first.
# If all predicates occuring at the leftside only occur at the leftside of all processed rules, then we process the rule at first.
def predicate_in_left_rule(predicates, rule):
    answer = True
    i = 0
    pos = find_position_in_list(rule, 'implies')[0]
    existing_predicates = predicate_in_rules(rule[0:pos])
    while i < len(existing_predicates) and answer:
        if existing_predicates[i] not in predicates:
            answer = False
        i = i + 1
    return answer

# Find suitable substitution
def predicate_existential_variables_instantiation(atoms, predicate, constants):
    substitution = []
    sub_temp = []
    atoms_rep=state_normal_representation(atoms)
    atoms = [atom for atom in atoms if atom["name"] == predicate["name"]]
    if not predicate["list_contain"]:
        predicate_copy = copy.deepcopy(predicate)
        for atom in atoms:
            flag = True
            for var in predicate["variables"]:
                i = 0
                while i < len(predicate_copy["values_in_non_list"]) and flag:
                    if predicate_copy["values_in_non_list"][i] in constants:
                        if atom["values_in_non_list"][i] != predicate_copy["values_in_non_list"][i]:
                            flag = False
                    else:
                        if predicate_copy["values_in_non_list"][i] == var:
                            predicate_copy["values_in_non_list"][i] = atom["values_in_non_list"][i]
                            sub_temp.append((var, atom["values_in_non_list"][i]))
                    i = i + 1
            if sub_temp != []:
                substitution.append(sub_temp)
                sub_temp = []
            predicate_copy = copy.deepcopy(predicate)
    else:
        predicate_copy = copy.deepcopy(predicate)
        for atom in atoms:
            flag = True
            if predicate_copy["values_in_list"][1] == [] and len(predicate_copy["values_in_list"][0]) == len(
                    atom["values_in_list"][0]):
                for var in predicate["variables"]:
                    i = 0
                    while i < len(predicate_copy["values_in_list"][0]) and flag:
                        if predicate_copy["values_in_list"][0][i] in constants:
                            if atom["values_in_list"][0][i] != predicate_copy["values_in_list"][0][i]:
                                flag = False
                        else:
                            if predicate_copy["values_in_list"][0][i] == var:
                                predicate_copy["values_in_list"][0][i] = atom["values_in_list"][0][i]
                                sub_temp.append((var, atom["values_in_list"][0][i]))
                        i = i + 1
                if sub_temp != []:
                    substitution.append(sub_temp)
                    sub_temp = []
                predicate_copy = copy.deepcopy(predicate)
            else:
                if len(predicate_copy["values_in_list"][0]) <= len(atom["values_in_list"][0]) and \
                        predicate_copy["values_in_list"][1] != []:
                    subtract = len(predicate_copy["values_in_list"][0]) - len(atom["values_in_list"][0])
                    list_var = predicate_copy["values_in_list"][1]
                    if len(predicate_copy["values_in_list"][0]) == len(atom["values_in_list"][0]):
                        sub_temp.append((list_var, []))
                    else:
                        second_list = atom["values_in_list"][0][subtract:]
                        sub_temp.append((list_var, second_list))

                    for var in predicate["variables"]:
                        i = 0
                        while i < len(predicate_copy["values_in_list"][0]) and flag:
                            if predicate_copy["values_in_list"][0][i] in constants:
                                if atom["values_in_list"][0][i] != predicate_copy["values_in_list"][0][i]:
                                    flag = False
                            else:
                                if predicate_copy["values_in_list"][0][i] == var:
                                    predicate_copy["values_in_list"][0][i] = atom["values_in_list"][0][i]
                                    sub_temp.append((var, atom["values_in_list"][0][i]))
                            i = i + 1
                    if flag:
                        predicate_copy["variables"].remove(list_var)
                        if sub_temp != []:
                            substitution.append(sub_temp)

                    predicate_copy = copy.deepcopy(predicate)
                    sub_temp = []
    return substitution

#Substitute a predicate with a substitution list.
def substitute_predicate(predicate, substitution):
    for sub in substitution:
        if sub[0] in predicate["variables"]:
            if predicate["list_contain"]:
                if predicate["values_in_list"][1] == sub[0]:
                    predicate["values_in_list"][1] = sub[1]
                    if sub[1] != []:
                        predicate["values_in_list"][0].extend(sub[1])
                        predicate["values_in_list"][1] = []
                else:
                    count = 0
                    while count < len(predicate["values_in_list"][0]):
                        if predicate["values_in_list"][0][count] == sub[0]:
                            predicate["values_in_list"][0][count] = sub[1]
                        count = count + 1
            else:
                count = 0
                while count < len(predicate["values_in_non_list"]):
                    if predicate["values_in_non_list"][count] == sub[0]:
                        predicate["values_in_non_list"][count] = sub[1]
                    count = count + 1
            predicate["variables"].remove(sub[0])
    return predicate

# instantiate the rule contianing variables to fully instantiated rules
def existential_variable_rule_instantiation(existential_rule, atoms, constants):
    existential_rule_rep=rule_normal_representation(existential_rule,constants)
    instantiated_rules = []
    instantiated_rules.append(existential_rule)
    i = 0
    while i < len(instantiated_rules):
        rule = copy.deepcopy(instantiated_rules[i])
        rule_copy = copy.deepcopy(rule)
        count = 0
        flag = True
        temp = []
        while count < len(rule) and flag:
            predicate = rule[count]
            if predicate not in keywords:
                if predicate["variables"] != []:
                    substitution = predicate_existential_variables_instantiation(atoms, predicate, constants)
                    if substitution != []:
                        flag = False
                        for sub in substitution:
                            rule_store = copy.deepcopy(rule)
                            temp = rule_store[:count]
                            for predicate in rule_store[count:]:
                                if predicate not in keywords:
                                    predicate_update = substitute_predicate(predicate, sub)
                                    temp.append(predicate_update)
                                else:
                                    temp.append(predicate)
                            instantiated_rules.append(temp)
                        instantiated_rules = [x for x in instantiated_rules if x != rule_copy]
                else:
                    temp.append(predicate)
            else:
                temp.append(predicate)
            count = count + 1
        if flag:
            i = i + 1
    return instantiated_rules


# Match the clause of the leftside of a rule with the atoms.
# If it can be matched with a atom, replace it with True, otherwise, replace it with False.
def pattern_mactch_at_left_rule(rule, atoms):
    pos = find_position_in_list(rule, 'implies')[0]
    i = 0
    flag = True
    while i < pos and flag:
        if rule[i] not in keywords:
            if rule[i] in atoms or rule[i] == True:
                rule[i] = True
                if i > 0 and rule[i - 1] == 'not':
                    flag = False
            else:
                rule[i] = False
                if i > 0 and rule[i - 1] != 'not':
                    flag = False
        i = i + 1
    return rule

# If all clause at the leftside of a rule are substitute with Boolean values, we can derive the atoms based on the rule.
# Due to closed world assumption, only True derives atoms.
def derivation_at_right_rule(rule):
    generated_atoms = []
    flag = True
    i = 0
    pos = find_position_in_list(rule, 'implies')[0]
    while i < pos and flag:
        if rule[i] not in keywords:
            if rule[i] != True and (i == 0 or rule[i - 1] != 'not'):
                flag = False
            elif rule[i] == True and (i > 0 and rule[i - 1] == 'not'):
                flag = False
        i = i + 1
    if flag:
        generated_atoms = rule[pos + 1:]
        # generated_atoms = [x for x in generated_atoms if x not in keywords]
    return generated_atoms

#Derive all atoms given a set of atoms, a set of fully instantiated rules, and a set of partial instantiated rules.
def atoms_derivation(atoms, fully_instantiated, partial_instantiated, constants):
    # If there is no more rules, then the atom generation process ends, return all atoms.
    if fully_instantiated == [] and partial_instantiated == []:
        return atoms
    # If there are at least one rule to be evaluate, start the derivation process
    else:
        predicates = []
        # Store all predicates occuring in all rules
        for rule in fully_instantiated + partial_instantiated:
            predicates = predicates + predicate_in_rules(rule)
        predicates = list(set(predicates))
        # Store the predicates only occuring at the leftside of rules
        predicates_at_left = []
        for i in predicates_position_in_rules(predicates, partial_instantiated + fully_instantiated):
            if i[1] == 'Left':
                predicates_at_left.append(i[0])
        # Store all rules which will be processed in the next step
        to_be_match = []
        signal = True
        initial = True
        while signal:
            if initial:
                for rule in partial_instantiated + fully_instantiated:
                    if predicate_in_left_rule(predicates_at_left, rule):
                        to_be_match.append(rule)
                partial_instantiated = [x for x in partial_instantiated if x not in to_be_match]
                fully_instantiated = [x for x in fully_instantiated if x not in to_be_match]
                initial = False
            else:
                to_be_match = partial_instantiated + fully_instantiated
            expand_rule = []
            for rule in to_be_match:
                if rule in fully_instantiated:
                    expand_rule.append(rule)
                else:
                    expand_rule = expand_rule + existential_variable_rule_instantiation(rule, atoms, constants)
            to_be_match = [x for x in expand_rule if x[-1] not in atoms]
            used = []
            interpreted = []
            for rule in to_be_match:
                interpreted.append(pattern_mactch_at_left_rule(rule, atoms))
            for i in interpreted:
                if derivation_at_right_rule(i) != []:
                    if derivation_at_right_rule(i)[0] not in atoms:
                        used.append(i)
                        atoms = atoms + derivation_at_right_rule(i)
            if used == []:
                signal = False
            to_be_match = partial_instantiated + fully_instantiated

    return atoms

#Derive all properties given a belief base, a knowledge base, and a domain.
def state_property_generation(belief_base, knowledge_base, domain, constants):
    rules = []
    belief_base_rep=state_normal_representation(belief_base)
    for i in knowledge_base:
        rules.append(i.split())
    for i in rules:
        if len(i) == 1:
            belief_base = belief_base + i
    rules = [x for x in rules if x[0] not in belief_base]
    M = separate_rules(rules, domain, constants)
    fully_instantiated = M[0]
    fully_instantiated_rep=rules_normal_representation(fully_instantiated,constants)
    partial_instantiated = M[1]
    partial_instantiated_copy=copy.deepcopy(partial_instantiated)
    partial_instantiated_rep=rules_normal_representation(partial_instantiated,constants)
    atoms_current = []
    for i in belief_base:
        if type(i) == type("1"):
            atoms_current.append(predicate_information(i, constants))
        else:
            atoms_current.append(i)
    atoms_current_rep=state_normal_representation(atoms_current)
    atoms = atoms_derivation(atoms_current, fully_instantiated, partial_instantiated, constants)
    atoms_rep=state_normal_representation(atoms)
    return atoms

#Instantiate a rule with a set of substitutions.
def rule_partial_instantiation(rule, substitutions):
    instantiated_rules = []
    for sub in substitutions:
        r = copy.deepcopy(rule)
        instantiated_rule = []
        for predicate in r:
            if predicate in keywords:
                instantiated_rule.append(predicate)
            else:
                instantiated_rule.append(substitute_predicate(predicate, sub))
        instantiated_rules.append(instantiated_rule)
    return instantiated_rules


#Evaluate if substates (i.e., agent states) are equal.
def equal_substate(state1, state2):
    flag = 0
    for i in state1:
        for j in state2:
            if i == j:
                flag = flag + 1
    if flag == len(state1) and flag==len(state2):
        return True
    else:
        return False


#Evaluate if a transition is included in the generated transitions.
def equal_transition(transitions, transition):
    flag=True
    for tr in transitions:
        for key in tr:
            if tr[key] == transition:
                flag = False
                break
    return flag

#Evaluate if a dictionary is empty.
def empty_dict(D):
    for key in D:
        if D[key]!=[]:
            return False
    return True

#Evaluate if the state properties is generated.
def exists_state_property(agent,state,state_properties_dict):
    for key in state_properties_dict:
        if agent in state_properties_dict[key].keys():
            state1 = state_properties_dict[key][agent][0][0]
            state1_rep = state_normal_representation(state1)
            state2 = state[0]
            state2_rep = state_normal_representation(state2)
            if equal_substate(state1, state2):
                return key
        else:
            return None
    return None

def generated_properties_evaluation(beliefs,belief_properties):
    i=0
    subset=None

    for b in belief_properties['B']:
        if set(b)==set(beliefs):
            return i
        elif set(b).issubset(set(beliefs)):
            subset=-i-1

        i=i+1

    return subset

def properties_generation(belief_base, belief_properties,belief_properties_rep,knowledge_base,domain,constants,dummy_flag):
    belief_base_rep=state_normal_representation(belief_base)
    generated_P = generated_properties_evaluation(belief_base_rep, belief_properties_rep)

    if generated_P == None:
        belief_properties['B'].append(belief_base)
        belief_properties_rep['B'].append(belief_base_rep)

        atom_current = state_property_generation(belief_base, knowledge_base, domain, constants)
        belief_properties['P'].append(atom_current)
        belief_properties_rep['P'].append(state_normal_representation(atom_current))
    elif generated_P<0:
        belief_properties['B'].append(belief_base)
        belief_properties_rep['B'].append(belief_base_rep)
        N = -generated_P - 1
        B = [x for x in belief_base or belief_properties['P'][N]]
        B_rep = state_normal_representation(B)
        atom_current = state_property_generation(B, knowledge_base, domain, constants)

        belief_properties['P'].append(atom_current)
        belief_properties_rep['P'].append(state_normal_representation(atom_current))
    else:
        atom_current = belief_properties['P'][generated_P]
    atom_current_rep = state_normal_representation(atom_current)
    return (belief_properties,belief_properties_rep,atom_current,atom_current_rep)

def action_constraints_analysis(action_constraints, atoms_current_state, atoms_goal_state, domain, constants):
    enabled_condition = []
    constraints = []
    All_Act_Cons_Name = []
    for constraint in action_constraints:
        constraints.append(constraint.split())
    instantiated_constraints=instatiate_rules(constraints,domain,constants)
    atoms_current_rep = state_normal_representation(atoms_current_state)
    goal_rep = state_normal_representation(atoms_goal_state)
    for constraint in instantiated_constraints:
        act_cons = constraint[-1]
        if act_cons['name'] not in All_Act_Cons_Name:
            All_Act_Cons_Name.append(act_cons['name'])
        fully_instantiated = existential_variable_rule_instantiation(constraint, atoms_current_state, constants)
        fully_instantiated_rep=rules_normal_representation(fully_instantiated,constants)
        for rule in fully_instantiated:
            new_rule = pattern_mactch_at_left_rule(rule, atoms_current_state)
            enabled = derivation_at_right_rule(new_rule)
            if enabled != []:
                enabled_rep=transform_to_normalform(enabled[0])
                enabled_condition.append(enabled)
    return (enabled_condition, All_Act_Cons_Name,fully_instantiated_rep)

def enabled_constraints_process(enabled_constraints, constants):
    enabled_constraints = sum(enabled_constraints, [])
    enabled_constraints_rep = state_normal_representation(enabled_constraints)
    enabled_constraints_rep = list(set(enabled_constraints_rep))
    enabled_constraints = []
    for i in enabled_constraints_rep:
        enabled_constraints.append(predicate_information(i, constants))
    return enabled_constraints

def action_enableness_analysis(action_enableness, atom_current_state, action_constraints, domain, All_Act_Cons_Name,constants):
    Act_Cons_Name = []
    for i in action_constraints:
        Act_Cons_Name.append(i['name'])
    Act_Cons_Name = list(set(Act_Cons_Name))

    atom_current_state_rep=state_normal_representation(atom_current_state)
    enabled_actions = []
    enableness_rule = []
    for enableness in action_enableness:
        enableness_rule.append(enableness.split())

    instantiated_constraints=instatiate_rules(enableness_rule,domain,constants)
    if predicate_information('fatal',constants) in atom_current_state:
        instantiated_constraints=[rule for rule in instantiated_constraints if (predicate_information('fatal',constants) in rule)]
    else:
        fatal_constraints=[rule for rule in instantiated_constraints if (predicate_information('fatal',constants) in rule)]
        instantiated_constraints=[rule for rule in instantiated_constraints if rule not in fatal_constraints]
    final_constraints = []
    for rule in instantiated_constraints:
        pos1 = find_position_in_list(rule, 'implies')[0]
        pos2 = find_position_in_list(rule, 'not')
        negative_predicates = []
        conclusion = rule[pos1 + 1]
        for pos in pos2:
            negative_predicates.append(rule[pos + 1])
        current_action_constraint = []
        flag_Act_Cons = True
        for predicate in rule[0:pos1]:
            if predicate not in keywords:
                if predicate["name"] in Act_Cons_Name:
                    current_action_constraint = predicate
                    break
                if predicate["name"] in All_Act_Cons_Name:
                    flag_Act_Cons = False
        if flag_Act_Cons:
            final_constraints.append(rule)
        if current_action_constraint != []:
            positive_predicates = [x for x in rule[0:pos1] if
                                   x not in negative_predicates and x != current_action_constraint and x not in keywords]
            operation_rule = []
            for predicate in positive_predicates:
                operation_rule.append(predicate)
                operation_rule.append("and")
            if negative_predicates != []:
                for predicate in negative_predicates:
                    operation_rule.append("not")
                    operation_rule.append(predicate)
                    operation_rule.append("and")
            operation_rule = operation_rule[:-1]
            operation_rule.append("implies")
            operation_rule.append(conclusion)
            if current_action_constraint in action_constraints:
                instanitated_rule = existential_variable_rule_instantiation(operation_rule, atom_current_state,constants)
                for rule in instanitated_rule:
                    new_rule = pattern_mactch_at_left_rule(rule, atom_current_state)
                    if derivation_at_right_rule(new_rule) != []:
                        enabled_actions = enabled_actions + derivation_at_right_rule(new_rule)
            else:
                substitution = predicate_existential_variables_instantiation(action_constraints,
                                                                             current_action_constraint,constants)
                if substitution != []:
                    new_operation_rules = []
                    for sub in substitution:
                        operation_rule_copy = copy.deepcopy(operation_rule)
                        new_rule = []
                        for predicate in operation_rule_copy:
                            if predicate not in keywords:
                                new_rule.append(substitute_predicate(predicate, sub))
                            else:
                                new_rule.append(predicate)
                        new_operation_rules.append(new_rule)
                    instanitated_rule = []
                    for rule in new_operation_rules:
                        instanitated_rule.extend(existential_variable_rule_instantiation(rule, atom_current_state,constants))
                        for rule in instanitated_rule:
                            new_rule = pattern_mactch_at_left_rule(rule, atom_current_state)
                            new_action = derivation_at_right_rule(new_rule)
                            if new_action != []:
                                if new_action[0] not in enabled_actions:
                                    enabled_actions = enabled_actions + new_action
    if enabled_actions == []:
        for rule in final_constraints:
            instanitated_rule = existential_variable_rule_instantiation(rule, atom_current_state,constants)
            for rule in instanitated_rule:
                new_rule = pattern_mactch_at_left_rule(rule, atom_current_state)
                en_Act = derivation_at_right_rule(new_rule)
                if en_Act != []:
                    if en_Act[0] not in enabled_actions:
                        enabled_actions = enabled_actions + en_Act
    return enabled_actions


def communication_analysis(current_agent, all_agents, sent_message_update, action_constraints, domain,
                           constants):
    sent_messages = []
    enableness_rule = []
    for enableness in sent_message_update:
        enableness_rule.append(enableness.split())

    instantiated_constraints = instatiate_rules(enableness_rule, domain, constants)
    if action_constraints != []:
        for constraint_copy in instantiated_constraints:
            constraint = copy.deepcopy(constraint_copy)
            Cons = existential_variable_rule_instantiation(constraint, action_constraints, constants)
            for cons in Cons:
                new_cons = pattern_mactch_at_left_rule(cons, action_constraints)
                new_cons_rep = rule_normal_representation(new_cons, constants)
                generated_info = derivation_at_right_rule(new_cons)
                generated_info_rep = rule_normal_representation(generated_info, constants)
                if generated_info != []:
                    message_type = generated_info[0]['name']
                    agent_info = generated_info[0]['values_in_non_list'][0]
                    if agent_info == 'all':
                        received_agents = all_agents
                    elif agent_info == 'allother':
                        received_agents = copy.deepcopy(all_agents)
                        received_agents.remove(current_agent)
                    else:
                        received_agents = [agent_info]
                    message_content = generated_info[1]
                    sent_messages.append((message_type, received_agents, message_content))
    return sent_messages
def transform_sent_msg(S):
    m=S[0]+'('+S[1][0]+')-' +transform_to_normalform(S[2])
    return m
def transform_received_msg(R):
    L=[]
    for r in R:
        m=r[0]+transform_to_normalform(r[1])
        L.append(m)
    return L
def enabled_events_generation(enabled,event_updates,atoms_current_state_copy,atoms_goal_state_copy,constants):
    if enabled[0] == "insert":
        if enabled[1] not in atoms_current_state_copy:
            event_updates['add_beliefs'].append(enabled[1])
            atoms_current_state_copy.append(enabled[1])
    elif enabled[0] == "delete":
        if enabled[1] in atoms_current_state_copy:
            event_updates["delete_beliefs"].append(enabled[1])
            atoms_current_state_copy.remove(enabled[1])
        elif enabled[1] == 'all':
            event_updates["delete_beliefs"] = atoms_current_state_copy
            atoms_current_state_copy = []
    elif enabled[0] == "adopt":
        if enabled[1] not in atoms_goal_state_copy and enabled[1] not in atoms_current_state_copy:
            event_updates['add_goals'].append(enabled[1])
            atoms_goal_state_copy.append(enabled[1])
            added_current_atom=copy.deepcopy(enabled[1])
            added_current_atom['name']='a-goal-'+added_current_atom['name']
            atoms_current_state_copy.append(added_current_atom)
    elif enabled[0] == "drop":
        if enabled[1] in atoms_goal_state_copy:# and enabled[1] in atoms_current_state_copy:
            event_updates["delete_goals"].append(enabled[1])
            atoms_goal_state_copy.remove(enabled[1])
        elif enabled[1]== 'all':
            event_updates["delete_goals"] = atoms_goal_state_copy
            atoms_goal_state_copy = []
            A=[]
            for atom in atoms_current_state_copy:
                if atom['name'][0:7]!='a-goal-':
                    A.append(atom)
            atoms_current_state_copy=copy.deepcopy(A)
        elif enabled[1]=='allgoals':
            event_updates["delete_goals"] =[predicate_information('allgoals',constants)]
            atoms_goal_state_copy = []
            atoms_current_state_copy=[]
    return (event_updates,atoms_current_state_copy,atoms_goal_state_copy)

def event_analysis(received_messages, event_processing, atoms_current_state, atoms_goal_state, domain, constants):
    event_updates = {"add_beliefs": [], "delete_beliefs": [], "add_goals": [], "delete_goals": [], "sent_messages": []}
    enableness_rule = []
    atoms_current_state_copy = copy.deepcopy(atoms_current_state)
    atoms_goal_state_copy = copy.deepcopy(atoms_goal_state)
    for enableness in event_processing:
        enableness_rule.append(enableness.split())
    instantiated_constraints = instatiate_rules(enableness_rule, domain, constants)

    communication_processing = []
    non_communication_processing = []
    communication_keywords = ["send:", "send!", "send?", "sent:", "sent!", "sent?"]
    for constraint in instantiated_constraints:
        flag = True
        for item in constraint:
            if item not in keywords:
                if item['name'] in communication_keywords:
                    flag = False
                    break
        if flag:
            non_communication_processing.append(constraint)
        else:
            communication_processing.append(constraint)
    atoms_current_rep = state_normal_representation(atoms_current_state_copy)
    goal_rep = state_normal_representation(atoms_goal_state_copy)
    processed_received_first_messages = []
    processed_received_second_messages = []
    flag_fatal_agent= False
    for m in received_messages:
        processed_received_first_messages.append(predicate_information(m[0], constants))
        processed_received_second_messages.append(m[1])
    for rule1 in instantiated_constraints:
        if flag_fatal_agent:
            break
        if rule1 in communication_processing:
            rule1_rep=rule_normal_representation(rule1,constants)
            if received_messages != []:
                rule_copy = copy.deepcopy(rule1)
                p1 = rule_copy[0]
                p2 = rule_copy[1]
                j = 0
                for msg in processed_received_first_messages:
                    sub1 = predicate_existential_variables_instantiation([msg], p1, constants)
                    sub2 = []
                    flag = False
                    if sub1 != []:
                        if p2['variables'] != []:
                            msg2 = processed_received_second_messages[j]
                            sub2 = predicate_existential_variables_instantiation([msg2], p2, constants)
                        elif p2['variables'] == [] and p2['values_in_non_list'] == ['_']:
                            msg2 = processed_received_second_messages[j]
                            if msg2['values_in_non_list'] != ['_']:
                                flag = True
                        if sub2 != []:
                            sub = [sub1[0] + sub2[0]]
                        else:
                            sub = sub1
                        if flag:
                            sub = []
                        rule_copy = copy.deepcopy(rule1)
                        partial_instantiated = rule_partial_instantiation(rule_copy, sub)
                        fully_instantiated = []
                        for rule in partial_instantiated:
                            fully_instantiated = fully_instantiated + existential_variable_rule_instantiation(rule,atoms_current_state_copy,constants)
                        fully_instantiated_rep = rules_normal_representation(fully_instantiated, constants)
                        for rule in fully_instantiated:
                            rule_rep=rule_normal_representation(rule,constants)
                            msg=(transform_to_normalform(rule[0]),rule[1])
                            if msg in received_messages:
                                new_rule = [True]
                                i = 2
                                while i < len(rule):
                                    new_rule.append(rule[i])
                                    i = i + 1
                                new_rule = pattern_mactch_at_left_rule(new_rule, atoms_current_state_copy)
                                enabled = derivation_at_right_rule(new_rule)
                                if enabled != []:
                                    if enabled[0] not in keywords:
                                        message_type = enabled[0]['name']
                                        received_agents = enabled[0]['values_in_non_list']
                                        msg = (message_type, received_agents, enabled[1])
                                        enabled_rep=transform_sent_msg(msg)
                                        event_updates["sent_messages"].append(msg)
                                    else:
                                        if enabled[1] == 'all' or enabled[1]=='allgoals':
                                            enabled_rep = enabled[0] + '-' + enabled[1]
                                        else:
                                            enabled_rep = enabled[0] + '-' + transform_to_normalform(enabled[1])
                                        E = enabled_events_generation(enabled, event_updates, atoms_current_state_copy,
                                                                      atoms_goal_state_copy,constants)
                                        event_updates = E[0]
                                        atoms_current_state_copy = E[1]
                                        atoms_goal_state_copy = E[2]
                    j = j + 1
        if rule1 in non_communication_processing:
            rule1_rep=rule_normal_representation(rule1,constants)
            partial_instantiated = [rule1]
            partial_instantiated_rep=rules_normal_representation(partial_instantiated,constants)
            fully_instantiated = []
            for rule in partial_instantiated:
                fully_instantiated = fully_instantiated + existential_variable_rule_instantiation(rule,
                                                                                                  atoms_current_state_copy,
                                                                                                  constants)
            fully_instantiated_rep=rules_normal_representation(fully_instantiated,constants)
            for rule in fully_instantiated:
                rule_rep = rule_normal_representation(rule, constants)
                rule = pattern_mactch_at_left_rule(rule, atoms_current_state_copy)
                enabled = derivation_at_right_rule(rule)
                if enabled != []:
                    if enabled[1]=='all' or enabled[1]=='allgoals':
                        enabled_rep=enabled[0]+'-'+enabled[1]
                    else:
                        enabled_rep=enabled[0]+'-'+transform_to_normalform(enabled[1])
                    E=enabled_events_generation(enabled,event_updates,atoms_current_state_copy,atoms_goal_state_copy,constants)
                    event_updates=E[0]
                    atoms_current_state_copy=E[1]
                    if E[1]==[]:
                        flag_fatal_agent=True
                    atoms_goal_state_copy=E[2]
    return event_updates

#Action only change the belief base.
def state_transformer(enable_actions, current_state, action_specification, domain,constants):
    current_beliefs = current_state
    cur_bel_rep = state_normal_representation(current_beliefs)
    Act_Name = []
    for i in enable_actions:
        Act_Name.append(i['name'])
    Act_Name = list(set(Act_Name))
    effect = []
    for key in action_specification:
        if key in Act_Name:
            effect.append(action_specification[key].split())

    instantiated_constraints = instatiate_rules(effect, domain, constants)
    next_state_beliefs = []
    for rule in instantiated_constraints:
        new_beliefs = copy.deepcopy(current_state)
        pos = find_position_in_list(rule, 'implies')[0]
        remove_predicates = []
        add_predicates = []
        previous_not = False
        flag=False
        for predicate in rule[0:pos]:
            if predicate not in keywords:
                if predicate["name"] in list(action_specification.keys()):
                    current_enabled_action = predicate
                    if predicate['variables']==[]:
                        flag=True
                    break
        substitution = predicate_existential_variables_instantiation(enable_actions, current_enabled_action,constants)
        if substitution != []:
            rule = [x for x in rule if x != current_enabled_action]
            rule_copy = copy.deepcopy(rule)

            for sub in substitution:
                count = 0
                while count < len(rule):
                    if rule[count] not in keywords:
                        rule[count] = substitute_predicate(rule[count], sub)
                    count = count + 1
                instantiated_rules = existential_variable_rule_instantiation(rule, current_beliefs,constants)
                for rule2 in instantiated_rules:
                    remove_predicates_copy = copy.deepcopy(remove_predicates)
                    add_predicates_copy = copy.deepcopy(add_predicates)
                    pos = find_position_in_list(rule2, 'implies')[0]
                    for predicate in rule2[pos + 1:]:
                        if predicate not in keywords:
                            if previous_not:
                                remove_predicates_copy.append(predicate)
                            else:
                                add_predicates_copy.append(predicate)
                            previous_not = False
                        elif predicate == 'not':
                            previous_not = True
                        else:
                            previous_not = False
                    new_rule = pattern_mactch_at_left_rule(rule2, current_beliefs)
                    if derivation_at_right_rule(new_rule) != []:
                        for predicate in add_predicates_copy:
                            new_beliefs.append(predicate)
                        for predicate in remove_predicates_copy:
                            new_beliefs.remove(predicate)
                        next_state_beliefs.append(new_beliefs)
                    new_beliefs = copy.deepcopy(current_state)
                rule = copy.deepcopy(rule_copy)
        elif flag:
            rule = [x for x in rule if x != current_enabled_action]
            remove_predicates_copy = copy.deepcopy(remove_predicates)
            add_predicates_copy = copy.deepcopy(add_predicates)
            pos = find_position_in_list(rule, 'implies')[0]
            for predicate in rule[pos + 1:]:
                if predicate not in keywords:
                    if previous_not:
                        remove_predicates_copy.append(predicate)
                    else:
                        add_predicates_copy.append(predicate)
                    previous_not = False
                elif predicate == 'not':
                    previous_not = True
                else:
                    previous_not = False
            new_rule = pattern_mactch_at_left_rule(rule, current_beliefs)
            if derivation_at_right_rule(new_rule) != []:
                for predicate in add_predicates_copy:
                    new_beliefs.append(predicate)
                for predicate in remove_predicates_copy:
                    new_beliefs.remove(predicate)
                next_state_beliefs.append(new_beliefs)

    return next_state_beliefs
#Test if state1 is a substate of state2.
def test_substate(state1, state2):
    if state1==[]:
        return False
    for i in state1:
        if i not in state2:
            return False
    return True

def equal_state(state1, state2):
    flag=True
    if state1.keys()==state2.keys():
        for key in state1:
            state1_beliefs=state1[key][0]
            state1_goals=state1[key][1]
            state2_beliefs = state2[key][0]
            state2_goals = state2[key][1]
            if not equal_substate(state1_beliefs,state2_beliefs) or state1_goals!=state2_goals:
                flag=False
    else:
        flag=False
    return flag

def state_reduction(state):
    reduced_state={}
    for key in state:
        if state[key][1]!=[]:
            reduced_state.update({key:(state[key][0],state[key][1][:1])})
        else:
            reduced_state.update({key:state[key]})
    return reduced_state

def system_error_check(state, System_Error_Messages,constants):
    for key in state:
        for error in System_Error_Messages:
            if predicate_information(error, constants) in state[key][0]:
                return True
    return False

def find_system_fatal_state(system):
    for key in system:
        state=system[key]
        for agent in state:
            B=state[agent][0]
            G=state[agent][1]
            if B==[] and G==[]:
                return key
    return 'None'


def remove_redundant_states(current_states, received_M_dict, remaining_goals_dict):
    i = 0
    checked_states = []
    Triple = []
    while i < len(current_states):
        current_state=current_states[i]
        for state in current_state:
            if state not in checked_states:
                checked_states.append(state)
                received_messages = received_M_dict[state]
                remaining_goals = remaining_goals_dict[state]
                j = 0
                if state in current_states[i + 1:]:

                    while j < len(received_messages):
                        triple = (current_state, received_messages[j], remaining_goals[j])
                        if triple not in Triple:
                            Triple.append(triple)
                        j = j + 1
                else:
                    triple = (current_state, received_messages[j], remaining_goals[j])
                    Triple.append(triple)

        i=i+1
    current_states = []
    received_M_dict = {}
    remaining_goals_dict = {}
    for (current_state, received_M, remaining_G) in Triple:
        current_states.append(current_state)
        for key in current_state:
            if key in received_M_dict.keys():
                received_M_dict[key].append(received_M)
            else:
                received_M_dict.update({key: [received_M]})
            if key in remaining_goals_dict.keys():
                remaining_goals_dict[key].append(remaining_G)
            else:
                remaining_goals_dict.update({key: [remaining_G]})


    return current_states, received_M_dict, remaining_goals_dict


def system_generation(agents, knowledge_base, constraints_of_action_generation,enableness_of_actions, action_specification, sent_message_update, event_processing,domain,constants,dummy_agents,prior_beliefs,Fatal_Error_Messgaes,System_Error_Messages):
    initial_state = {}
    initial_state_rep = {}
    #Record intial goals of each agent within the autonomous system
    initial_remaining_goals={}
    all_agents_name=[]
    for agent in agents:
        if prior_beliefs!=[]:
            if agent.name not in dummy_agents:
                agent.belief_base.extend(prior_beliefs)
        all_agents_name.append(agent.name)
        B = process_bliefs(agent.belief_base,constants)
        G = process_belief_list(agent.goals,constants)
        if G!=[]:
            initial_remaining_goals.update({agent.name:G[1:]})
            initial_state.update({agent.name:(B,G[:1])})
        else:
            initial_remaining_goals.update({agent.name: []})
            initial_state.update({agent.name: (B, G)})

        normal_B = state_normal_representation(B)
        normal_G = state_list_normal_representation(G[:1])
        initial_state_rep.update({agent.name: (normal_B, normal_G)})
    initial_remaining_goals_rep=system_goals_normal_representation(initial_remaining_goals)
    if prior_beliefs!=[]:
        processed_prior_beliefs = process_bliefs(prior_beliefs, constants)
        prior_beliefs_name = []
        for b in processed_prior_beliefs:
            if b['name'] not in prior_beliefs_name:
                prior_beliefs_name.append(b['name'])

    system = {}
    system_rep={}
    state = {}
    state_next_states_dict={}
    transitions = []
    count_transition = 1
    count_goal = 0
    state_transitions_dict = {}
    belief_properties={'B':[],'P':[]}
    belief_properties_rep={'B':[],'P':[]}
    state_properties = {}
    state_properties_rep = {}
    if prior_beliefs!=[]:
        state_prior_beliefs_dict={'I':processed_prior_beliefs}
        state_prior_beliefs_rep_dict={'I':prior_beliefs}
    else:
        state_prior_beliefs_rep_dict ={}
    count = 1


    initial_state_copy=copy.deepcopy(initial_state)
    system['I'] = initial_state_copy
    system_rep['I'] =transform_multi_states_normal(system['I'])

    initial_rep = system_state_normal_representation(initial_state_copy)
    current_states = [{"I": initial_state}]
    current_states_rep = [{"I": initial_rep}]
    adopted_goals_dict = {}
    adopted_goals_dict_rep = {}
    received_messages={}
    for agent in agents:
        received_messages.update({agent.name:agent.received_messages})
    received_M_dict = {'I':[received_messages]}
    remaining_goals_dict = {'I': [initial_remaining_goals]}
    remaining_goals_dict_rep = {'I': [initial_remaining_goals_rep]}

    while current_states != []:
        all_s = []
        for s in current_states:
            all_s.extend(s.keys())
        #print(all_s)
        received_M_dict_new = {}
        remaining_goals_dict_new = {}

        next_states=[]
        next_states_rep=[]
        substate_dict = {}
        substate_dict_rep = {}
        substate_properties_dict = {}
        substate_properties_dict_rep = {}
        current_states_copy=copy.deepcopy(current_states)

        count_item=0
        empty_received_M={}
        for agent in agents:
            empty_received_M.update({agent.name:[]})

        for item in current_states_copy:
            enabled_action_dict = {}
            enabled_action_dict_rep = {}
            enabled_sent_messages_dict = {}

            for key in item:
                state_key = copy.deepcopy(key)
                state = item[key]
            current_state = key
            #print(current_state)

            if current_state=='S72':
                MM=1
            if current_state=='S2':
                MM=1



            N_item = current_states_copy[:count_item + 1].count(key)
            #print(current_state,system_goals_normal_representation(remaining_goals_dict[current_state]))
            processed_received_messages = {}
            if current_state in received_M_dict.keys():
                processed_received_messages=copy.deepcopy(received_M_dict[current_state][N_item])
            else:
                received_M_dict.update({current_state: [empty_received_M]})

            if system_error_check(state, System_Error_Messages, constants):
                state_keys=[current_state]
                if current_state not in state_next_states_dict.keys():
                    next_state={}
                    next_state_rep = []
                    for agent in state:
                        B=state[agent][0]
                        for error in System_Error_Messages:
                            e=predicate_information(error, constants)
                            new_E = predicate_information('System_Crash', constants)
                            if e in B:
                                if agent in next_state.keys():
                                    next_state[agent][0].append(new_E)
                                else:
                                    next_state.update({agent: ([new_E], [])})
                    next_state_rep=transform_multi_states_normal(next_state)
                    flag=True
                    for k in system:
                        if equal_state(next_state, system[k]):
                            flag = False
                            break
                    if flag:
                        state_keys.append("S" + str(count))
                        next_states.append({"S" + str(count): next_state})
                        transitions.append(
                            {"Transition" + str(count_transition): (current_state, ['System Crashed'], "S" + str(count))})
                        state_next_states_dict.update({current_state: [(['System Crashed'],{"S" + str(count): next_state},empty_received_M)]})
                        system["S" + str(count)] = next_state
                        system_rep["S" + str(count)] = next_state_rep
                        count = count + 1
                    else:
                        state_keys.append(k)
                        next_states.append({k: system[k]})
                        transitions.append(
                            {"Transition" + str(count_transition): (current_state, ['System Crashed'], k)})
                        state_next_states_dict.update({current_state: [(['System Crashed'],k,empty_received_M)]})
                    count_transition = count_transition + 1
                for key in state_keys:
                    state=system[key]
                    for name in state:
                        current_belief_base = state[name][0]
                        P = properties_generation(current_belief_base, belief_properties, belief_properties_rep,
                                          knowledge_base, domain, constants, dummy_flag)
                        belief_properties = P[0]
                        belief_properties_rep = P[1]
                        atom_current = P[2]
                        atom_current_rep = P[3]
                        if key in state_properties.keys():
                            state_properties[key][name] = ([state[name], atom_current])
                            state_properties_rep[key][name] = state_normal_representation(atom_current)
                        else:
                            state_properties.update({key: {name: [state[name], atom_current]}})
                            state_properties_rep.update(
                                {key: {name: state_normal_representation(atom_current)}})

                state_transitions_dict.update(
                            {current_state: [("Transition" + str(count_transition), ['System Crashed'])]})




            else:
                flag_compute = False
                if current_state in state_next_states_dict.keys():
                    if current_state=='S10':
                        MM=1
                    NS = []
                    next_received_M_dict={}
                    for (received_M, key, next_RM) in state_next_states_dict[current_state]:
                        if processed_received_messages==received_M:
                            NS.append({key:system[key]})
                            next_received_M_dict.update({key: next_RM})

                    if NS!=[]:
                        if current_state=='S10':
                            MM=1
                        old_states = []
                        new_states = []

                        count_NS = 0

                        next_state_remaining_goals={}

                        for s in NS:
                            flag_trans=False
                            transition=[]
                            for next in s:
                                for trans in transitions:
                                    for key in trans:
                                        if trans[key][0] == current_state and trans[key][2] == next:
                                            transition = trans[key][1]
                                            flag_trans = True
                                            break
                                    if flag_trans:
                                        break

                            state_remaining_goals = copy.deepcopy(remaining_goals_dict[current_state][N_item])
                            new_state_remaining_goals = copy.deepcopy(state_remaining_goals)
                            for key in s:
                                next_received_messages = copy.deepcopy(next_received_M_dict[key])
                                for name in system[key]:
                                    for item in system[key][name][0]:
                                        if transform_to_normalform(item) in Fatal_Error_Messgaes:
                                            new_state_remaining_goals[name] = []
                                            break
                                next_state_remaining_goals.update({key: new_state_remaining_goals})


                            new_S = copy.deepcopy(system[key])

                            for agent in agents:
                                name = agent.name
                                next_goal = new_S[name][1]
                                if name not in dummy_agents:
                                    # The goal depends on the next remaining goal.
                                    if next_goal != []:
                                        if len(next_goal[0]) == 1:
                                            agent_remaining_goals = copy.deepcopy(new_state_remaining_goals[name])
                                            next_goal_rep = state_list_normal_representation(next_goal)
                                            if next_goal_rep[0] in agent.goals:
                                                remaining_goals = copy.deepcopy(agent_remaining_goals)
                                                next_state_remaining_goals[key][name] = remaining_goals[1:]
                                                new_S[name] = (new_S[name][0], [])
                                                if remaining_goals != []:
                                                    new_S[name] = (new_S[name][0], remaining_goals[:1])
                                    else:
                                        agent_remaining_goals = copy.deepcopy(new_state_remaining_goals[name])
                                        if agent_remaining_goals != []:
                                            new_S[name] = (new_S[name][0], agent_remaining_goals[:1])
                                            next_state_remaining_goals[key][name] = agent_remaining_goals[1:]

                            flag = True
                            next_state = key
                            if not equal_state(new_S, system[key]):
                                for k in system:
                                    if equal_state(new_S, system[k]):
                                        flag = False
                                        if key not in old_states:
                                            old_states.append({key: system[key]})
                                        if k not in new_states:
                                            new_states.append({k: system[k]})
                                        next_state=k

                                        if (processed_received_messages, k, next_received_messages) not in state_next_states_dict[current_state]:
                                            state_next_states_dict[current_state].append(
                                                (processed_received_messages, k, next_received_messages))

                                        tr = (current_state, transition, k)
                                        if current_state!=k:
                                            if equal_transition(transitions, tr):
                                                transitions.append({"Transition" + str(count_transition): tr})
                                                count_transition = count_transition + 1
                                            break


                            else:

                                flag = False
                            if flag:

                                if key not in old_states:
                                    old_states.append({key: system[key]})
                                new_states.append({'S' + str(count): new_S})

                                state_remaining_goals = copy.deepcopy(next_state_remaining_goals[key])
                                remaining_goals_dict_new.update({'S' + str(count): [state_remaining_goals]})
                                received_M_dict_new.update({"S" + str(count): [next_received_messages]})



                                system.update({"S" + str(count): new_S})

                                system_rep.update({"S" + str(count): transform_multi_states_normal(new_S)})

                                if current_state in state_next_states_dict.keys():
                                    if (processed_received_messages, "S" + str(count), next_received_messages) not in state_next_states_dict[
                                        current_state]:
                                        state_next_states_dict[current_state].append((processed_received_messages, "S" + str(count), next_received_messages))
                                else:
                                    state_next_states_dict.update({current_state: [(processed_received_messages, "S" + str(count), next_received_messages)]})
                                transitions.append(
                                    {"Transition" + str(count_transition): (
                                    current_state, transition, "S" + str(count))})
                                key = 'S' + str(count)
                                for agent in agents:
                                    name = agent.name
                                    substate = new_S[name]
                                    current_belief_base = substate[0]
                                    focused_goal_base = substate[1]
                                    focused_goal_base_rep = state_list_normal_representation(focused_goal_base)
                                    P = properties_generation(current_belief_base, belief_properties,
                                                              belief_properties_rep,
                                                              knowledge_base, domain, constants, dummy_flag)
                                    belief_properties = P[0]
                                    belief_properties_rep = P[1]
                                    atom_current = P[2]
                                    atom_current_rep = P[3]

                                    if key in state_properties.keys():
                                        state_properties[key][name] = ([state[name], atom_current])
                                        state_properties_rep[key][name] = state_normal_representation(atom_current)
                                    else:
                                        state_properties.update({key: {name: [state[name], atom_current]}})
                                        state_properties_rep.update(
                                            {key: {name: state_normal_representation(atom_current)}})
                                count = count + 1
                                count_transition = count_transition + 1
                                count_NS = count_NS + 1
                            else:
                                state_remaining_goals = copy.deepcopy(next_state_remaining_goals[key])
                                if next_state not in remaining_goals_dict_new.keys():
                                    remaining_goals_dict_new.update({next_state: [state_remaining_goals]})
                                else:
                                    remaining_goals_dict_new[next_state].append(state_remaining_goals)
                                if next_state in received_M_dict_new.keys():
                                    received_M_dict_new[next_state].append(next_received_messages)
                                else:
                                    received_M_dict_new.update({next_state: [next_received_messages]})
                                count_NS = count_NS + 1
                            if next_state=='S79':
                                MM=1


                        NS = [x for x in NS if x not in old_states]

                        NS=NS+new_states
                        next_states = next_states + NS
                    else:
                        flag_compute = True



                if flag_compute or current_state not in state_next_states_dict.keys():

                    key=current_state
                    if key=='S3':
                        MM=1
                    state_remaining_goals = copy.deepcopy(remaining_goals_dict[state_key][N_item])
                    new_substate_remaining_goals_dict = {}
                    new_substate_remaining_goals_rep_dict = {}

                    for agent in agents:
                        enabled_sent_messages = []
                        name = agent.name
                        remaining_goals = state_remaining_goals[name]
                        dummy_flag = False
                        if name in dummy_agents:
                            dummy_flag = True
                        active_flag = True

                        # Evaluate if the agent is inactive by check if it contains fatal error messages.
                        for item in state[name][0]:
                            if transform_to_normalform(item) in Fatal_Error_Messgaes:
                                active_flag = False
                                break
                        # An agent will drop all goals if it encounters a fatal error.
                        if not active_flag:
                            new_substate_remaining_goals_dict.update({name: []})
                            state[name] = (state[name][0], [])
                            substate_dict[name] = (state[name][0], [])

                        # substate_goal stores te state generate at each subgoal level (for each agent)
                        substate = state[name]
                        current_belief_base = substate[0]
                        focused_goal_base = substate[1]
                        focused_goal_base_rep = state_list_normal_representation(focused_goal_base)
                        P = properties_generation(current_belief_base, belief_properties, belief_properties_rep,
                                                  knowledge_base, domain, constants, dummy_flag)

                        belief_properties = P[0]
                        belief_properties_rep = P[1]
                        atom_current = P[2]
                        atom_current_rep = P[3]
                        if key in state_properties.keys():
                            state_properties[key][name] = ([state[name], atom_current])
                            state_properties_rep[key][name] = state_normal_representation(atom_current)
                        else:
                            state_properties.update({key: {name: [state[name], atom_current]}})
                            state_properties_rep.update({key: {name: state_normal_representation(atom_current)}})

                        atom_current_desired = copy.deepcopy(atom_current)
                        atom_current_desired_rep = state_normal_representation(atom_current_desired)
                        if focused_goal_base == [] and remaining_goals == [] and not dummy_flag:
                            enabled_action_dict[name] = []
                            substate_dict.update({name: substate})
                            substate_dict_rep.update({name: transform_mental_states_normal(substate)})
                            atom_current_desired = copy.deepcopy(atom_current)
                            enabled_sent_messages_dict.update({name: enabled_sent_messages})



                        elif focused_goal_base != [] and active_flag and not dummy_flag :

                            substate_dict.update({name: substate})

                            substate_dict_rep.update({name: transform_mental_states_normal(substate)})

                            atom_current_rep = state_normal_representation(atom_current)

                            substate_properties_dict.update({name: atom_current})

                            substate_properties_dict_rep.update({name: atom_current_rep})

                            # Current focus is the MAS is focusing on.

                            if substate[1] != []:
                                current_focus = substate[1][0]
                            else:
                                current_focus = []

                            current_focus_rep = state_normal_representation(current_focus)

                            P = properties_generation(current_focus, belief_properties, belief_properties_rep,

                                                      knowledge_base, domain, constants, dummy_flag)

                            belief_properties = P[0]

                            belief_properties_rep = P[1]

                            atom_goal = P[2]

                            atom_goal_rep = P[3]

                            if atom_goal != []:

                                desired_beliefs = []

                                for atom in atom_goal:

                                    if atom not in atom_current:

                                        atom_copy = copy.deepcopy(atom)

                                        atom_copy['name'] = 'a-goal-' + atom_copy['name']

                                        if atom_copy not in atom_current:
                                            desired_beliefs.append(atom_copy)

                                atom_current_desired.extend(desired_beliefs)

                                atom_current_desired_rep = state_normal_representation(atom_current_desired)

                            ACA = action_constraints_analysis(constraints_of_action_generation, atom_current_desired,

                                                              atom_goal, domain,

                                                              constants)

                            enabled_constraints = ACA[0]

                            All_Act_Cons_Name = ACA[1]

                            enabled_constraints = sum(enabled_constraints, [])

                            enabled_constraints_rep = state_normal_representation(enabled_constraints)

                            enabled_constraints_rep = list(set(enabled_constraints_rep))

                            enabled_constraints = []

                            for i in enabled_constraints_rep:
                                enabled_constraints.append(predicate_information(i, constants))

                            enabled_actions = action_enableness_analysis(enableness_of_actions, atom_current,

                                                                         enabled_constraints, domain, All_Act_Cons_Name,

                                                                         constants)

                            enabled_actions_rep = state_normal_representation(enabled_actions)

                            enabled_action_dict.update({name: enabled_actions})

                            enabled_action_dict_rep.update({name: enabled_actions_rep})

                            if enabled_actions == []:
                                enabled_sent_messages = communication_analysis(name, all_agents_name,
                                                                               sent_message_update,

                                                                               enabled_constraints, domain, constants)

                            enabled_sent_messages_dict.update({name: enabled_sent_messages})

                            agent.sent_messages = agent.sent_messages + enabled_sent_messages



                        elif dummy_flag:

                            substate_dict.update({name: substate})

                            substate_dict_rep.update({name: transform_mental_states_normal(substate)})
                            # state propeties is the same as the current beliefs
                            atom_current_rep = state_normal_representation(atom_current)
                            atom_goal = []
                            atom_current_desired = atom_current
                            atom_current_desired_rep = state_normal_representation(atom_current_desired)

                            substate_properties_dict.update({name: atom_current})

                            substate_properties_dict_rep.update({name: atom_current_rep})

                            ACA = action_constraints_analysis(constraints_of_action_generation, atom_current_desired,
                                                              atom_goal, domain,

                                                              constants)

                            enabled_constraints = ACA[0]

                            All_Act_Cons_Name = ACA[1]

                            enabled_constraints = sum(enabled_constraints, [])

                            enabled_constraints_rep = state_normal_representation(enabled_constraints)

                            enabled_constraints_rep = list(set(enabled_constraints_rep))

                            enabled_constraints = []

                            for i in enabled_constraints_rep:
                                enabled_constraints.append(predicate_information(i, constants))

                            enabled_sent_messages = communication_analysis(name, all_agents_name, sent_message_update,

                                                                           enabled_constraints, domain,

                                                                           constants)

                            enabled_sent_messages_dict.update({name: enabled_sent_messages})

                            agent.sent_messages = agent.sent_messages + enabled_sent_messages

                        else:
                            enabled_sent_messages_dict.update({name: []})
                            substate_dict.update({name: substate})
                            substate_dict_rep.update({name: transform_mental_states_normal(substate)})
                            atom_current_rep = state_normal_representation(atom_current)
                            substate_properties_dict.update({name: atom_current})
                            substate_properties_dict_rep.update({name: atom_current_rep})
                        if active_flag:
                            last_received_messages=received_M_dict[key][N_item][name]

                            enabled_event_update = event_analysis(last_received_messages, event_processing,
                                                                  atom_current_desired, atom_goal,
                                                                  domain, constants)
                            if enabled_event_update['sent_messages'] != []:
                                agent.sent_messages = agent.sent_messages + enabled_event_update['sent_messages']
                                enabled_sent_messages_dict[agent.name] = agent.sent_messages

                            inserted_beliefs = enabled_event_update['add_beliefs']
                            inserted_beliefs_rep = state_normal_representation(inserted_beliefs)
                            deleted_beliefs = enabled_event_update['delete_beliefs']
                            deleted_beliefs_rep = state_normal_representation(deleted_beliefs)
                            adopted_goals = enabled_event_update['add_goals']
                            adopted_goals_rep = state_normal_representation(adopted_goals)
                            dropped_goals = enabled_event_update['delete_goals']
                            dropped_goals_rep = state_normal_representation(dropped_goals)

                            if deleted_beliefs != []:
                                new_beliefs = [x for x in substate_dict[name][0] if x not in deleted_beliefs]
                                substate_dict[name] = (new_beliefs, substate_dict[name][1])
                            if inserted_beliefs != []:
                                substate_dict[name] = (
                                substate_dict[name][0] + inserted_beliefs, substate_dict[name][1])

                            fatal_flag = False
                            if dropped_goals == [predicate_information('allgoals', constants)]:
                                substate_dict[name] = (inserted_beliefs, [])
                                new_substate_remaining_goals_dict.update({name: []})
                                fatal_flag = True
                                state_remaining_goals[name] = []
                            elif dropped_goals != []:
                                if substate_dict[name][1] != []:
                                    substate_goal_copy = copy.deepcopy(substate_dict[name][1][0])
                                    for goal in dropped_goals:
                                        if goal in substate_goal_copy:
                                            substate_goal_copy.remove(goal)
                                    if substate_goal_copy != []:
                                        substate_dict[name] = (
                                            substate_dict[name][0], [substate_goal_copy])
                                    elif substate_goal_copy == [] and adopted_goals == []:
                                        substate_dict[name] = (substate_dict[name][0], [[]])
                                    else:
                                        substate_dict[name] = (substate_dict[name][0], [[]])


                            if adopted_goals != [] and not fatal_flag:
                                for goal in adopted_goals:
                                    if goal not in substate_dict[name][1][0]:
                                        substate_dict[name] = (
                                            substate_dict[name][0],
                                            [substate_dict[name][1][0] + [goal]])
                                        substate_dict_rep[name] = transform_mental_states_normal(substate_dict[name])
                            if name in adopted_goals_dict.keys() and not fatal_flag:
                                adopted_goals_dict[name] = adopted_goals_dict[name] + adopted_goals
                                adopted_goals_dict_rep[name] = adopted_goals_dict_rep[name] + adopted_goals_rep
                            else:
                                adopted_goals_dict.update({name: adopted_goals})
                                adopted_goals_dict_rep.update({name: adopted_goals_rep})

                    new_substate_dict = {}
                    new_substate_rep_dict = {}

                    original_state_remaing_goals = copy.deepcopy(state_remaining_goals)
                    for agent in agents:
                        possible_next_beliefs = []
                        name = agent.name
                        if name not in new_substate_remaining_goals_dict.keys():
                            new_substate_remaining_goals_dict.update({name: []})
                            new_substate_remaining_goals_rep_dict.update({name: []})
                        if name in dummy_agents:
                            dummy_flag = True
                        else:
                            dummy_flag = False
                        substate = substate_dict[name]
                        current_belief_base = substate[0]
                        current_belief_base_rep = state_normal_representation(current_belief_base)
                        subgoal = substate_dict[name][1]
                        subgoal_rep = state_list_normal_representation(subgoal)

                        subgoal_copy = copy.deepcopy(subgoal)

                        temporary_goals = adopted_goals_dict[name]
                        temporary_goals_rep = adopted_goals_dict_rep[name]
                        flag_next=False
                        if name in enabled_action_dict.keys():
                            if enabled_action_dict[name] != []:
                                flag_next = True
                                en_actions = enabled_action_dict[name]
                                possible_next_beliefs = possible_next_beliefs + state_transformer(en_actions,
                                                                                                  current_belief_base,
                                                                                                  action_specification,
                                                                                                  domain, constants)
                                possible_next_beliefs_rep = state_list_normal_representation(possible_next_beliefs)


                        if not flag_next:
                            possible_next_beliefs.append(current_belief_base)
                            possible_next_beliefs_rep = state_list_normal_representation(possible_next_beliefs)

                        for item in possible_next_beliefs:
                            agent_remaining_goals = copy.deepcopy(original_state_remaing_goals[name])
                            P = properties_generation(item, belief_properties, belief_properties_rep,
                                                      knowledge_base,
                                                      domain, constants, dummy_flag)
                            belief_properties = P[0]
                            belief_properties_rep = P[1]
                            atoms_item = P[2]
                            atoms_item_rep = P[3]

                            new_subgoal = copy.deepcopy(subgoal)
                            new_subgoal_rep = state_list_normal_representation(new_subgoal)

                            if subgoal != []:
                                for goal in subgoal_copy[0]:
                                    if goal in atoms_item and goal in new_subgoal[0]:
                                        new_subgoal[0].remove(goal)
                                        if goal in temporary_goals:
                                            if goal in adopted_goals_dict[name]:
                                                adopted_goals_dict[name].remove(goal)
                                                adopted_goals_dict_rep[name].remove(
                                                    transform_to_normalform(goal))
                                        if new_subgoal == [[]]:
                                            new_subgoal = []
                                        substate_dict[name] = (substate_dict[name][0], new_subgoal)

                            if new_subgoal != []:
                                P = properties_generation(new_subgoal[0], belief_properties,
                                                          belief_properties_rep,
                                                          knowledge_base,
                                                          domain, constants, dummy_flag)
                            else:
                                P = properties_generation([], belief_properties,
                                                          belief_properties_rep,
                                                          knowledge_base,
                                                          domain, constants, dummy_flag)

                            belief_properties = P[0]
                            belief_properties_rep = P[1]
                            atoms_subgoal = P[2]
                            atoms_subgoal_rep = P[3]

                            # The current goal is achieved.
                            if test_substate(atoms_subgoal, atoms_item):
                                if agent_remaining_goals != []:
                                    focused_goal = agent_remaining_goals[:1]
                                    new_agent_remaining_goals = agent_remaining_goals[1:]
                                else:
                                    focused_goal = []
                                    new_agent_remaining_goals = []

                                adopted_goals_dict[name] = []
                                adopted_goals_dict_rep[name] = []
                                if name in new_substate_dict.keys():
                                    new_substate_dict[name].append((item, focused_goal))
                                    new_substate_rep_dict[name].append((state_normal_representation(item),
                                                                        state_list_normal_representation(
                                                                            focused_goal)))

                                else:
                                    new_substate_dict.update({name: [(item, focused_goal)]})
                                    new_substate_rep_dict.update({name: [(state_normal_representation(item),
                                                                          state_list_normal_representation(
                                                                              focused_goal))]})

                                new_substate_remaining_goals_dict[name].append(new_agent_remaining_goals)
                            # The current goal is not accomplished.
                            else:
                                new_agent_remaining_goals = copy.deepcopy(agent_remaining_goals)
                                if name in new_substate_dict.keys():
                                    new_substate_dict[name].append((item, new_subgoal))
                                    new_substate_rep_dict[name].append(
                                        (state_normal_representation(item), new_subgoal_rep))

                                else:
                                    new_substate_dict.update({name: [(item, new_subgoal)]})
                                    new_substate_rep_dict.update(
                                        {name: [(state_normal_representation(item), new_subgoal_rep)]})
                                new_substate_remaining_goals_dict[name].append(new_agent_remaining_goals)
                                if new_agent_remaining_goals != []:
                                    new_substate_remaining_goals_rep_dict[name].append(
                                        state_list_normal_representation(new_agent_remaining_goals))



                    possible_next_states = [{}]
                    possible_next_states_remaining_goals = [{}]
                    current_state_info_copy = copy.deepcopy(state)
                    current_state_info_rep = transform_multi_states_normal(current_state_info_copy)
                    enabled_action_sent_messages_flatten = [[]]

                    for key in new_substate_dict:
                        possible_next_states_new = []
                        possible_next_states_remaining_goals_new = []
                        i = 0
                        for substate in new_substate_dict[key]:
                            j = 0
                            for item in possible_next_states:
                                item_copy = copy.deepcopy(item)
                                item_copy.update({key: substate})
                                possible_next_states_new.append(item_copy)
                                state_remaining_goals_copy = copy.deepcopy(possible_next_states_remaining_goals[j])
                                state_remaining_goals_copy.update({key: []})
                                if i < len(new_substate_remaining_goals_dict[key]):
                                    state_remaining_goals_copy[key] = new_substate_remaining_goals_dict[key][i]

                                if possible_next_states_remaining_goals_new == []:
                                    possible_next_states_remaining_goals_new = [state_remaining_goals_copy]
                                else:
                                    possible_next_states_remaining_goals_new.append(state_remaining_goals_copy)
                                j = j + 1
                            i = i + 1
                        possible_next_states = copy.deepcopy(possible_next_states_new)
                        possible_next_states_remaining_goals = copy.deepcopy(
                            possible_next_states_remaining_goals_new)
                        enabled_action_sent_messages_flatten_new = []
                        if key in enabled_action_dict.keys() and enabled_action_dict[key] != []:
                            enabled_action_sent_messages_flatten_new = []
                            for action in enabled_action_dict_rep[key]:
                                action_info = key + str(": ") + action
                                for item in enabled_action_sent_messages_flatten:
                                    enabled_action_sent_messages_flatten_new.append(item + [action_info])

                        if (enabled_sent_messages_dict[key] != [] and substate_dict[key][
                            1] != []) or key in dummy_agents:
                            sent_messages = []
                            for en_msg in enabled_sent_messages_dict[key]:
                                M = transform_to_normalform(en_msg[-1])
                                en_msg_reform = copy.deepcopy(en_msg)
                                en_msg_reform = (en_msg_reform[0], en_msg_reform[1], M)
                                sent_msg_info = key + str(": ") + str(en_msg_reform)
                                sent_messages.append(sent_msg_info)

                            for item in enabled_action_sent_messages_flatten:
                                enabled_action_sent_messages_flatten_new.append(item + sent_messages)

                        if enabled_action_sent_messages_flatten_new != []:
                            enabled_action_sent_messages_flatten = copy.deepcopy(
                                enabled_action_sent_messages_flatten_new)


                    # Only actions can change the prior beliefs.
                    # Only when the number of active agents is greater than 1, we need to calibrate the prior beliefs.
                    # Calculate the number of active agents
                    if prior_beliefs != []:
                        prior_beliefs_list = []
                        prior_beliefs = state_prior_beliefs_dict[state_key]
                        prior_beliefs_rep = state_prior_beliefs_rep_dict[state_key]
                        if empty_dict(enabled_action_dict):
                            prior_beliefs_list = [state_prior_beliefs_dict[state_key]] * len(possible_next_states)
                        else:
                            for state in possible_next_states:
                                old_prior_B = copy.deepcopy(prior_beliefs)
                                old_prior_B_rep = copy.deepcopy(prior_beliefs_rep)

                                delete_beliefs = []
                                delete_beliefs_rep = []
                                add_beliefs = []
                                add_beliefs_rep = []
                                for name in state:
                                    beliefs = copy.deepcopy(state[name][0])
                                    beliefs_rep = state_normal_representation(beliefs)
                                    prior_B = []
                                    active_flag = True
                                    if transform_to_normalform(state[name][0][0]) in Fatal_Error_Messgaes:
                                        active_flag = False
                                    if name not in dummy_agents and active_flag:
                                        for b in beliefs:
                                            if b['name'] in prior_beliefs_name:
                                                prior_B.append(b)
                                        prior_B_rep = state_normal_representation(prior_B)
                                        add_beliefs_rep.extend(list(set(prior_B_rep) - set(old_prior_B_rep)))
                                        delete_beliefs_rep.extend(list(set(old_prior_B_rep) - set(prior_B_rep)))
                                PB = list(set(old_prior_B_rep).union(set(add_beliefs_rep)))
                                new_prior_B_rep = [x for x in PB if x not in delete_beliefs_rep]
                                new_prior_B = process_bliefs(new_prior_B_rep, constants)
                                if set(new_prior_B_rep) != set(old_prior_B_rep):
                                    for name in state:
                                        active_flag = True
                                        if transform_to_normalform(state[name][0][0]) in Fatal_Error_Messgaes:
                                            active_flag = False
                                        beliefs = copy.deepcopy(state[name][0])
                                        beliefs_rep = state_normal_representation(beliefs)
                                        goals = copy.deepcopy(state[name][1])
                                        updated_beliefs = []
                                        if name not in dummy_agents and active_flag:
                                            for b in beliefs:
                                                if b['name'] not in prior_beliefs_name:
                                                    updated_beliefs.append(b)
                                            updated_beliefs.extend(new_prior_B)
                                            state[name] = (updated_beliefs, goals)

                                prior_beliefs_list.append(new_prior_B)



                    for agent in agents:
                        agent.received_messages = []
                    for agent in agents:
                        sender_name = agent.name
                        if agent.sent_messages != []:
                            for sent_message in agent.sent_messages:
                                receivers_name = sent_message[1]
                                receivers = []
                                for name in receivers_name:
                                    for a in agents:
                                        if a.name == name:
                                            receivers.append(a)
                                            break
                                for receiver in receivers:
                                    if sent_message[0] == "send:":
                                        msg = "sent:(" + sender_name + ")"
                                        receiver.received_messages.append((msg, sent_message[2]))
                                    elif sent_message[0] == "send!":
                                        msg = "sent!(" + sender_name + ")"
                                        receiver.received_messages.append((msg, sent_message[2]))
                                    else:
                                        msg = "sent?(" + sender_name + ")"
                                        receiver.received_messages.append((msg, sent_message[2]))
                        agent.sent_messages = []

                    next_received_M={}
                    for agent in agents:
                        name=agent.name
                        next_received_M.update({name:agent.received_messages})
                    i = 0
                    while i < len(possible_next_states):
                        state = possible_next_states[i]
                        state_remaining_goals = possible_next_states_remaining_goals[i]
                        if prior_beliefs != []:
                            state_prior_beliefs = prior_beliefs_list[i]
                        if i < len(enabled_action_sent_messages_flatten):
                            communication = enabled_action_sent_messages_flatten[i]
                        else:
                            communication = []

                        flag = True
                        for key in system:
                            if equal_state(state, system[key]):
                                flag = False
                                next_state = key
                                flag_add = True
                                for next in next_states:
                                    if not flag_add:
                                        break
                                    for id in next:
                                        if id == key:
                                            flag_add = False
                                            break
                                if flag_add:
                                    next_states.append({key: system[key]})
                                break

                        if flag:
                            next_states.append({"S" + str(count): state})
                            if count=='72':
                                MM=1
                            if prior_beliefs != []:
                                state_prior_beliefs_dict.update({"S" + str(count): state_prior_beliefs})
                                state_prior_beliefs_rep_dict.update(
                                    {"S" + str(count): state_normal_representation(state_prior_beliefs)})

                            transitions.append(
                                {"Transition" + str(count_transition): (current_state, communication, "S" + str(count))})
                            if current_state in state_next_states_dict.keys():
                                if (processed_received_messages, "S" + str(count),next_received_M) not in state_next_states_dict[current_state]:
                                    state_next_states_dict[current_state].append(
                                        (processed_received_messages, "S" + str(count), next_received_M))

                            else:
                                state_next_states_dict.update({current_state: [(processed_received_messages,"S" + str(count),next_received_M)]})


                            received_M_dict_new.update({"S" + str(count): [next_received_M]})

                            remaining_goals_dict_new.update({"S" + str(count): [state_remaining_goals]})
                            count_transition = count_transition + 1
                            system["S" + str(count)] = state
                            system_rep["S" + str(count)] = transform_multi_states_normal(state)
                            count = count + 1
                        else:
                            next_states.append({next_state: state})


                            if current_state in state_next_states_dict.keys():
                                # Only record the result of communication
                                if current_state != next_state:
                                    if (processed_received_messages,next_state) not in state_next_states_dict[current_state]:
                                        state_next_states_dict[current_state].append((processed_received_messages,next_state,next_received_M))
                            else:
                                if current_state != next_state:
                                    state_next_states_dict.update({current_state: [(processed_received_messages,next_state,next_received_M)]})

                            if next_state in received_M_dict_new.keys():
                                received_M_dict_new[next_state].append(next_received_M)
                            else:
                                received_M_dict_new.update({next_state: [next_received_M]})

                            if next_state not in remaining_goals_dict_new.keys():
                                remaining_goals_dict_new.update({next_state: [state_remaining_goals]})
                            else:
                                remaining_goals_dict_new[next_state].append(state_remaining_goals)

                            if current_state!=next_state:
                                tr = (current_state, communication, next_state)
                                if equal_transition(transitions, tr):
                                    transitions.append({"Transition" + str(count_transition): (
                                        current_state, communication, next_state)})
                                    count_transition = count_transition + 1


                        i = i + 1

            count_item = count_item + 1



        next_states=[x for x in next_states if not test_final_state(x)]
        current_states = next_states


        received_M_dict=copy.deepcopy(received_M_dict_new)

        remaining_goals_dict_rep={}
        remaining_goals_dict=copy.deepcopy(remaining_goals_dict_new)
        for state in current_states:
            for key in state:
                if key=='S72':
                    MM=1
                if key=='S2':
                    MM=1
            if current_states.count(state)>1:
                current_states,received_M_dict,remaining_goals_dict=remove_redundant_states(current_states,received_M_dict,remaining_goals_dict)

        for key in remaining_goals_dict:
            remaining_goals_dict_rep.update({key:[]})
            for remaining_goals in remaining_goals_dict[key]:
                remaining_goals_dict_rep[key].append(system_goals_normal_representation(remaining_goals))


    if len(system) ==1:
        print("No system")
        return None

    final_states=[]
    for s in system:
        if test_final_state({s:system[s]}):
            final_states.append({s:system[s]})

    for final_state in final_states:
        for key in final_state:
            state=final_state[key]
        for name in state:
            if name in dummy_agents:
                dummy_flag=True
            else:
                dummy_flag=False
            substate = state[name]
            current_belief_base = substate[0]
            P = properties_generation(current_belief_base, belief_properties, belief_properties_rep, knowledge_base,
                                      domain, constants, dummy_flag)
            belief_properties = P[0]
            belief_properties_rep = P[1]
            atom_current = P[2]
            atom_current_rep = P[3]
            if key in state_properties_rep.keys():
                state_properties_rep[key][name] = atom_current_rep
            else:
                state_properties_rep.update({key: {name: atom_current_rep}})

    return (system_rep,transitions,state_properties_rep,state_prior_beliefs_rep_dict,belief_properties_rep,system,state_next_states_dict,remaining_goals_dict,final_states)

