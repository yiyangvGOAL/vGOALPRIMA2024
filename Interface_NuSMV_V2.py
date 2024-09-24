#For a property P, find its key in the dictionary storing properties.
def symbol_property(agent,P,dict_properties):
    symbol=[]
    for p in P:
        for k in dict_properties:
            if dict_properties[k]==(agent,p):
                symbol.append(k)
                break
    return symbol

def property_processing(properties, safety_properties, Fatal_Error_Messgaes, System_Error_Messages,crash_properties, error_properties):
    #store all safety properties in a symbolic way
    safety_symbol_property = {}
    fatal_properties = {}
    F_properties=[]
    S_properties = []
    C_properties = []
    E_properties = []
    E_type_properties = {}
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
            if agent in safety_properties.keys():
                if p in safety_properties[agent]:
                    if agent in safety_symbol_property.keys():
                        safety_symbol_property[agent].append("p" + str(count_p))
                    else:
                        safety_symbol_property.update({agent: ["p" + str(count_p)]})
            if p in Fatal_Error_Messgaes:
                if agent in fatal_properties.keys():
                    fatal_properties[agent].append("p" + str(count_p))
                else:
                    fatal_properties.update({agent: ["p" + str(count_p)]})
            if p in Fatal_Error_Messgaes:
                if "p" + str(count_p) not in F_properties:
                    F_properties.append("p" + str(count_p))
            if p in System_Error_Messages:
                if "p" + str(count_p) not in S_properties:
                    S_properties.append("p" + str(count_p))
            if p in crash_properties:
                if "p" + str(count_p) not in C_properties:
                    C_properties.append("p" + str(count_p))


            if p in error_properties:
                E_properties.append("p" + str(count_p))
            if p in error_properties:
                if p not in E_type_properties.keys():
                    E_type_properties.update({p: ["p" + str(count_p)]})
                else:
                    E_type_properties[p].append("p" + str(count_p))

            count_p = count_p + 1
        # A dictionary store state and its proeprty in the symbolic way.
        s_properties_normal = {}

        for key in properties:
            s_properties_normal[key] = {}
            for agent in properties[key]:
                s_properties_normal[key][agent] = symbol_property(agent, properties[key][agent], dict_properties)
    return s_properties_normal,safety_symbol_property,fatal_properties,F_properties, S_properties,C_properties, E_properties, E_type_properties


def property_state_generation(s_properties_normal):
    property_state={}
    for state in s_properties_normal:
        for agent in s_properties_normal[state]:
            for p in s_properties_normal[state][agent]:
                if p not in property_state.keys():
                    property_state.update({p:[state]})
                else:
                    property_state[p].append(state)
    return property_state

def interface_generation(system, transitions, properties,safety_properties,Fatal_Error_Messgaes,System_Error_Messages, crash_properties,final_states,error_properties):
    N, safety_symbol_properties,fatal_properties, F_properties, system_error_properties, crash_properties, error_properties, error_type_properties =property_processing(properties,safety_properties,Fatal_Error_Messgaes, System_Error_Messages,crash_properties, error_properties)
    property_state=property_state_generation(N)
    f = open("test1.smv", "w+")
    f.write("MODULE main" + '\n')
    f.write("VAR" + '\n')
    state = "   state : {" + ", ".join(system) + "};\n"
    f.write(state)
    f.write("ASSIGN\n")
    f.write("   init(state) := I;\n\n")
    f.write("   next(state) := case\n")
    next_state_dict={}
    for t in transitions:
        for key in t:
            cur=t[key][0]
            next=t[key][-1]
            if cur not in next_state_dict.keys():
                next_state_dict.update({cur:[next]})
            else:
                next_state_dict[cur].append(next)
    for cur in next_state_dict:
        next=next_state_dict[cur]
        f.write("      state = " + cur + " : {" + ", ".join(next) + "};\n")
    f.write("      TRUE :state;\n")
    f.write("   esac;\n")
    f.write("DEFINE\n")
    for p in property_state:
        f.write("   " + p + " := ")
        for state in property_state[p]:
            f.write("state = " + state + " | ")
        f.write("FALSE;\n")
    f.write("--CTL Properties\n")
    f.write("CTLSPEC AG TRUE")
    for agent in safety_symbol_properties:
        f.write(" & ((")
        for p in safety_symbol_properties[agent]:
            f.write(p + " & ")
        f.write("TRUE)")
        for p in fatal_properties[agent]:
            f.write(" | " + p)
        f.write(")")
    f.write("\n")
    f.write("CTLSPEC EG ((")
    for p in error_properties:
        f.write("!"+p + " & ")
    f.write("TRUE) -> EF (")
    for state in final_states:
        for key in state:
            f.write("state = " + key + " | ")
    f.write("FALSE))\n")
    f.close()
    return safety_symbol_properties, fatal_properties, F_properties, system_error_properties, crash_properties,error_properties,error_type_properties
