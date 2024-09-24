import copy
import os

import TS_Generation as TG


# For a property P, find its key in the dictionary storing properties.
def symbol_property(agent, P, dict_properties):
    symbol = []
    for p in P:
        for k in dict_properties:
            if dict_properties[k] == (agent, p):
                symbol.append(k)
                break
    return symbol


# Given a state, search the key in the state dictionary.
def state_search(s, state_check):
    for key in state_check:
        if key == s:
            return state_check[key]


def state_map2(states):
    dict_state = {}
    count = 0
    for s in states:
        if s == 'I':
            dict_state.update({count: s})
        else:
            dict_state.update({count: s})
        count = count + 1
    return dict_state


# Map state to a number
def state_map(states):
    state_check = {}
    count = 0
    for s in states:
        if s == 'I':
            state_check.update({s: count})
        else:
            state_check.update({s: count})
        count = count + 1
    return state_check


def state_search2(s, state_check):
    for key in state_check:
        if state_check[key] == s:
            return key


def action_search(action, dict_actions):
    loop = len(action)
    i = 1
    result = "("
    for item in action:
        for key in dict_actions:
            if item == dict_actions[key]:
                if i < loop:
                    result = result + key + ','

                else:
                    result = result + key + ')'
                    return result
                break
        i = i + 1


def map_transition(transition, dict_state, dict_actions):
    return ((state_search2(transition[0], dict_state), action_search(transition[1], dict_actions),
             state_search2(transition[2], dict_state)))


# Simulate an action based on the given probabilities
def simulate_action(action, action_probability):
    actions = []
    for key in action_probability.keys():
        if action.startswith(key):
            actions.append(action.split("(")[0])
            break

    if actions == []:
        return 1.0  # Default to the action itself with probability 1 if no probability is specified

    return action_probability[actions[0]]


def get_transition_probability(transition, action_probability):
    starting_state, actions, _ = transition
    total_probability = 1.0

    for action in actions:
        action_type = action.split(':')[-1].strip()
        probability = simulate_action(action_type, action_probability)
        total_probability *= probability

    return total_probability


def probability_adjustment(trans):
    state_transition_probability = {}
    trans_copy = copy.deepcopy(trans)
    for key in trans_copy:
        P = 0
        for (s, p) in trans_copy[key]:
            P = P + p
        if P == 1:
            state_transition_probability.update({key: trans_copy[key]})
        else:
            state_distribution = []
            for (s, p) in trans_copy[key]:
                state_distribution.append((s, p / P))
            state_transition_probability.update({key: state_distribution})

    return state_transition_probability


def interface_generation(system, transitions, properties, action_probability, constants):
    # Compute all distict properties.
    property_list = []
    for key in properties:
        for agent in properties[key]:
            property_list = property_list + (properties[key][agent])
    property_list = list(set(property_list))

    property_dict = {}
    for key in properties:
        for agent in properties[key]:
            if agent not in property_dict.keys():
                property_dict.update({agent: []})
            for p in properties[key][agent]:
                if p not in property_dict[agent]:
                    property_dict[agent].append(p)
    # Store all properties in a dictionary, and assign a name to each property
    dict_properties2 = {}
    count_p = 1
    for p in property_list:
        dict_properties2.update({"p" + str(count_p): p})
        count_p = count_p + 1
    dict_properties = {}
    count_p = 1
    for agent in property_dict:
        for p in property_dict[agent]:
            dict_properties.update({"p" + str(count_p): (agent, p)})
            count_p = count_p + 1
    # trans is a dictionary storing all next states of the current state with the corresponding probability.
    trans = {}
    for n in transitions:
        for key in n:
            transition = n[key]
            p = get_transition_probability(transition, action_probability)
            if n[key][0] not in trans.keys():

                trans.update({n[key][0]: [(n[key][2], p)]})
            else:
                t = n[key][0]
                trans[t].append((n[key][2], p))
    trans = probability_adjustment(trans)
    # A dictionary store state and its proeprty in the symbolic way.
    s_properties_normal = {}

    for key in properties:
        s_properties_normal[key] = {}
        for agent in properties[key]:
            s_properties_normal[key][agent] = symbol_property(agent, properties[key][agent], dict_properties)

    # Extract all states
    system_states = []
    for s in system:
        system_states.append(s)

    # A dictionary storing the states
    dict_state = state_map(system_states)
    dict_state2 = state_map2(system_states)
    actions = []
    for transition in transitions:
        for key in transition:
            act = transition[key][1]
            actions = actions + act
    actions = list(set(actions))
    dict_actions = {}
    count_act = 1
    for act in actions:
        flag = True
        for key in dict_actions:
            if act == dict_actions[key]:
                flag = False
                break
        if flag:
            dict_actions.update({"action" + str(count_act): act})
            count_act = count_act + 1
    nonfinal_states = []
    for i in transitions:
        for key in i:
            T = map_transition(i[key], dict_state2, dict_actions)
            if T[0] not in nonfinal_states:
                nonfinal_states.append(T[0])

    final_states = [x for x in range(0, len(system)) if x not in nonfinal_states]

    final_state = state_search("S" + str(len(system) - 1), dict_state)
    # Generate the interface to Prism/Storm
    f = open("test1.pm", "w+")
    f.write("dtmc" + '\n' + '\n')
    f.write("module test" + '\n')
    f.write("  s: [0.." + str(len(system) - 1) + "]  init 0 ;" + '\n')
    # Initialize all properties based on their value in the initial state.
    initial = []
    for key in s_properties_normal['I']:
        initial = initial + s_properties_normal['I'][key]
    for i in dict_properties:
        f.write("  " + i + ":bool")  # +'  init false;\n')
        if i in initial:
            f.write('   init true;\n')
        else:
            f.write('   init false;\n')
    f.write("\n")
    for s in final_states:
        trans.update({'S' + str(s): [('S' + str(s), 1)]})
    for t in trans:

        if t == 'S2':
            MM = 1
        if len(trans[t]) == 1:
            f.write("     []")
            P1 = []
            for agent in s_properties_normal[t]:
                P1 = P1 + s_properties_normal[t][agent]
            current_s = state_search(t, dict_state)
            f.write('s=' + str(current_s))
            for key in dict_properties:
                if key in P1:
                    f.write('  &(' + key + '= true)  ')
                else:
                    f.write('  &(' + key + '= false)  ')

            P2 = []
            for agent in s_properties_normal[trans[t][0][0]]:
                P2 = P2 + s_properties_normal[trans[t][0][0]][agent]
            next_s = state_search(trans[t][0][0], dict_state)

            f.write("->" + "(s'=" + str(next_s) + ')')
            for key in dict_properties:
                if key in P2:
                    f.write('  &(' + key + '\'= true)  ')
                else:
                    f.write('  &(' + key + '\'= false)  ')
            f.write(';\n')
        else:

            f.write("     []")
            P1 = []
            for agent in s_properties_normal[t]:
                P1 = P1 + s_properties_normal[t][agent]

            current_s = state_search(t, dict_state)
            f.write('s=' + str(current_s))
            for key in dict_properties:
                if key in P1:
                    f.write('  &(' + key + '= true)  ')
                else:
                    f.write('  &(' + key + '= false)  ')

            P2 = []
            for agent in s_properties_normal[trans[t][0][0]]:
                P2 = P2 + s_properties_normal[trans[t][0][0]][agent]
            next_s = state_search(trans[t][0][0], dict_state)
            f.write("->" + str(trans[t][0][1]) + ": (s'=" + str(next_s) + ')')
            for key in dict_properties:
                if key in P2:
                    f.write('  &(' + key + '\'= true)  ')
                else:
                    f.write('  &(' + key + '\'= false)  ')
            next_states = trans[t][1:]
            for (s, p) in next_states:
                P2 = []
                for agent in s_properties_normal[s]:
                    P2 = P2 + s_properties_normal[s][agent]
                next_s = state_search(s, dict_state)
                f.write(" + " + str(p) + ": (s'=" + str(next_s) + ')')
                for key in dict_properties:
                    if key in P2:
                        f.write('  &(' + key + '\'= true)  ')
                    else:
                        f.write('  &(' + key + '\'= false)  ')
            f.write(";\n")
    f.write("\n\n endmodule")

    f.close()
    f = open("Specifications01.txt", "w+")
    f.write("The states are:\n")
    for key in dict_state2:
        f.write(str(key) + ": " + dict_state2[key] + '\n')
    f.write("The actions are:\n")
    for key in dict_actions:
        f.write(key + ": " + ''.join(dict_actions[key]) + '\n')
    f.write("The properties are:\n")

    for key in dict_properties:
        f.write(key + ": " + ''.join(dict_properties[key]) + '\n')

    f.close()

    return


def write_property_formula(f, formula_str, model_idx):
    f.write(f"  formula_str_{model_idx} = \"{formula_str}\"\n")
    f.write(f"  properties_{model_idx} = stormpy.parse_properties(formula_str_{model_idx}, prism_program)\n")
    f.write(f"  model_{model_idx} = stormpy.build_model(prism_program, properties_{model_idx})\n")
    f.write(f"  result_{model_idx} = stormpy.model_checking(model_{model_idx}, properties_{model_idx}[0])\n")
    f.write(f"  initial_state_{model_idx} = model_{model_idx}.initial_states[0]\n")
    f.write(f"  print(result_{model_idx}.at(initial_state_{model_idx}))\n")

def property_file_generation(final_states, safety_symbol_properties, fatal_properties, F_properties, system_error_properties, crash_properties, error_properties):
    with open("PCTL.py", "w+") as f:
        f.write("import stormpy\n")
        f.write("import time\n")
        f.write("def main():\n")
        f.write("  path = \"test1.pm\"\n")
        f.write("  start = time.time()\n")
        f.write("  prism_program = stormpy.parse_prism_program(path)\n")
        f.write("  mid = time.time()\n")
        f.write("  print(\"Time to parse the model: \", mid - start)\n")

        # Formula 1
        formula_str_1 = "P=? [G ("
        first_agent = True
        for agent in safety_symbol_properties:
            if first_agent:
                formula_str_1 += " ("
                first_agent = False
            else:
                formula_str_1 += " | (("
            formula_str_1 += " & ".join(safety_symbol_properties[agent]) + " )|"
            formula_str_1 += " | ".join(F_properties) + ")"
        formula_str_1 += "]"
        write_property_formula(f, formula_str_1, 1)

        # Formula 2
        formula_str_2 = "P=? [("
        formula_str_2 += " & ".join(f"!{p}" for p in error_properties)
        formula_str_2 += ") U ("
        formula_str_2 += " & ".join(f"!{p}" for p in error_properties)
        formula_str_2 += "& ("
        formula_str_2 += " | ".join(f"s= {key[1:]}" for state in final_states for key in state)
        formula_str_2 += "))]"
        write_property_formula(f, formula_str_2, 2)
        i = 3
        f.write("  print(\"The probability of at least one error is:\")\n")
        formula = "formula_str_" + str(i)
        formula = "P=? [ F (" + " | ".join(error_properties) + ")]"
        write_property_formula(f, formula, i)
        i = i + 1
        f.write("  print(\"The probability of system crash is:\")\n")
        formula = "formula_str_" + str(i)
        formula = "P=? [ F (" + " & ".join(crash_properties) + ")]"
        write_property_formula(f, formula, i)
        i = i + 1
        f.write("  print(\"Errors and system crashes\")\n")

        for error in error_properties:
            formula="formula_str_" + str(i)
            formula="P=? [(!" + error + ") U (!"+error+" & "
            formula += " & ".join(crash_properties) + ")]"
            write_property_formula(f, formula, i)
            i=i+1
        f.write("  print(\"The probability of fatal agents is:\")\n")
        formula = "formula_str_" + str(i)
        formula = "P=? [ F (" + " | ".join(F_properties) + ")]"
        write_property_formula(f, formula, i)
        i = i + 1
        f.write("  print(\"Errors and fatal agents\")\n")
        for error in error_properties:
            formula="formula_str_" + str(i)
            formula="P=? [(!" + error + ") U (!"+error+" & "
            formula += " | ".join(F_properties) + ")]"
            write_property_formula(f, formula, i)
            i=i+1


        f.write("  end = time.time()\n")
        f.write("  print(\"The time for model checking is: \", end - mid)\n")
        f.write("  return result_3\n")
        f.write("if __name__ == \"__main__\":\n")
        f.write("  main()\n")

    return


def property_file_generation2(crash_properties, error_properties):
    with open("PCTL.py", "w+") as f:
        f.write("import stormpy\n")
        f.write("import time\n")
        f.write("def main():\n")
        f.write("  path = \"test1.pm\"\n")
        f.write("  start = time.time()\n")
        f.write("  prism_program = stormpy.parse_prism_program(path)\n")
        #f.write("  mid = time.time()\n")
        #f.write("  print(\"Time to parse the model: \", mid - start)\n")
        i = 1
        #f.write("  print(\"The probability of system crash is:\")\n")
        formula = "formula_str_" + str(i)
        formula = "P=? [ F (" + " | ".join(crash_properties) + ")]"
        write_property_formula(f, formula, i)
        i = i + 1
        for error in error_properties:
            formula="formula_str_" + str(i)
            formula="P=? [(!" + error + ") U (!"+error+" & ("
            formula += " | ".join(crash_properties) + "))]"
            write_property_formula(f, formula, i)
            i=i+1

        f.write("  end = time.time()\n")
        #f.write("  print(\"The time for PCTL model checking is: \", end - start, \"s\")\n")
        #f.write("  print( end - start)\n")
        f.write("if __name__ == \"__main__\":\n")
        f.write("  main()\n")

    return

def property_file_generation3(crash_properties, error_type_properties):
    with open("PCTL.py", "w+") as f:
        f.write("import stormpy\n")
        f.write("import time\n")
        f.write("def main():\n")
        f.write("  path = \"test1.pm\"\n")
        f.write("  start = time.time()\n")
        f.write("  prism_program = stormpy.parse_prism_program(path)\n")
        i = 1
        formula = "formula_str_" + str(i)
        formula = "P=? [ F (" + " | ".join(crash_properties) + ")]"
        write_property_formula(f, formula, i)
        i = i + 1
        for E in error_type_properties:
            formula="formula_str_" + str(i)
            formula="P=? [(!" + " & !".join(error_type_properties[E]) + ") U (!"+ " & !".join(error_type_properties[E]) + " & (" + " | ".join(crash_properties) + "))]"
            #error=error_type_properties[E]
            #formula+= "& !".join(error) + ") U ("
            #formula += " | ".join(crash_properties) + ")]"
            write_property_formula(f, formula, i)
            i=i+1

        f.write("  end = time.time()\n")
        #f.write("  print(\"The time for PCTL model checking is: \", end - start, \"s\")\n")
        #f.write("  print( end - start)\n")
        f.write("if __name__ == \"__main__\":\n")
        f.write("  main()\n")

    return
