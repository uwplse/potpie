import argparse
import os
import sys
import glob
import subprocess
import re

prints_proof_loc = False
prints_spec_loc = False
prints_per_file = False
has_max_level = False

def get_args():
    ap = argparse.ArgumentParser()

    ap.add_argument("files", nargs="*", type=str, help="Files to count lines of code for")
    ap.add_argument("--amp", "-a", action="store_true", help="Insert & in between columns (for LaTeX tables). This also turns meta-categories into \multicolumn{n}{c|}{<column name>}")
    ap.add_argument("--space-nicely", action="store_true", help="If the --amp option is given, this will still space out header rows nicely so they can be copy and pasted into spreadsheets for further manipulation. Has no effect when --amp is not given.")
    ap.add_argument("--proof-loc", "-p", action="store_true", help="Output LOC of proof")
    ap.add_argument("--spec-loc", action="store_true", help="Output LOC of specs")
    ap.add_argument("--split-loc", action="store_true", help="Output LOC of spec and proof, this subsumes --proof-loc and --spec-loc")
    ap.add_argument("--cat", "-c", action="append", help="Only include specified categories")
    ap.add_argument("--output", choices=["stdout", "csv"], default="stdout", help="Where to put the output. Default is stdout. If csv, this overrides the --amp option.")
    ap.add_argument("--index", action="store_true", help="Print out a column on the left hand side of what all of the columns mean.")
    ap.add_argument("--per-file", action="store_true", help="Print out columns per file name instead of per category")
    ap.add_argument("--collapse", action="append", help="Collapse certain categories of files")
    ap.add_argument("--expand", action="append", help="Expand certain categories of files to be per-file")
    ap.add_argument("--other", action="store_true", help="Just print out the files that end up in the \"Other\" category -- this is for determining what files may be missing from the current categorization.")
    ap.add_argument("--omit", action="append", help="Omit a column or category")
    ap.add_argument("--max-level", type=int, default=-1, help="Specify a maximum depth to make the header row.")
    ap.add_argument("--verbose", "-v", action="store_true", help="Print out extra information")
    ap.add_argument("--include-ml", action="store_true", help="Include .ml files when calculating LOC")

    return ap.parse_args()

default_files_sep = {
    "Imp": {
        "Lang": ["Base.v", "Imp_LangDec.v", "Imp_LangTrickLanguage.v", "Imp_LangTrickSemanticsMutInd.v"],
        "Logic": ["Imp_LangLogHoare.v","Imp_LangLogProp.v","Imp_LangLogPropDec.v","Imp_LangLogSubst.v","Imp_LangLogSubstAdequate.v","ProofSubstitution.v",],
        "WF": ["Imp_LangImpHigherOrderRel.v","Imp_LangImpHigherOrderRelTheorems.v","ImpVarMap.v","ImpVarMapTheorems.v","ParamsWellFormed.v","ParamsWellFormedMutInd.v","FunctionWellFormed.v","Imp_LangHoareWF.v",]
    },
    "Stack": {
        "Lang": ["StackLangTheorems.v","StackLanguage.v","StackSemanticsMutInd.v","StackSubstitution.v","StackDec.v","StackUpdateAdequacy.v","StackExtensionDeterministic.v",],
        "Logic": ["StackLogic.v","StackLogicBase.v","StackLogicGrammar.v",],
        "WF": ["StackFrame.v","StackFrame1.v","StackFrameBase.v","StackFrameMin.v","StackFrameMinHelpers.v","StackFrameZ.v","StackFrameZTheorems.v","StackPure.v","StackPurest.v","StackPurestBase.v","StackExprWellFormed.v",],
    },
    "Base": {
        "Props": ["LogicProp.v","LogicPropDec.v","LogicPropTheorems.v",],
    },
    "Compiler": {
        "Code": ["EnvToStack.v", "CompilerCorrectHelpers.v","CompilerCorrectMoreHelpers.v","FactEnvTranslator.v",],
        "Spec": ["LogicTranslationBase.v","LogicTranslationCompilerAgnostic.v","FactEnvTranslator.v",],
        "\\flowA": ["ProofCompilerBase.v","ProofCompilerHelpers.v","ProofCompilerPostHelpers.v","ProofCompCodeCompAgnosticMod.v","ProofCompilerCodeCompAgnostic.v","ProofCompilableCodeCompiler.v","UIPList.v",],
        "\\flowB": ["HoareTree.v","StkHoareTree.v","StateUpdateAdequacy.v","TreeProofCompiler.v","CoqCoreInductives.ml","aimpstk.ml", "boolChecker.ml", "checker.ml", "checkerConstants.ml", "collections.ml", "contextutils.ml", "coqOptions.ml", "defutils.ml", "g_hoarechecker.mlg", "induction.ml", "locationutils.ml", "printingutils.ml", "stateutils.ml", "stkhoaretree.ml", "stkvalidtree.ml", "termutils.ml", "utilities.ml"],

    },
    "Instantiations": ["EnvToStackBuggy.v","EnvToStackIncomplete.v","EnvToStackLTtoLEQ.v","BuggyProofCompiler.v","UnprovenCorrectProofCompiler.v","IncompleteProofCompiler.v",],
    "Examples": {
        "Small": ["ExampleLeftShift_Incomplete.v","MaxIncorrectProofCompilationExample.v","MaxUnprovenCorrectProofCompilationExample.v","MinProofCompilationExample.v",],
        "Multiplication": {
            "Core": ["Multiplication", "MultWrappers.v"],
            "Tree": ["MultiplicationTreeCompiled.v"],
            "TreeC": ["MultiplicationTreeCorrect.v"],
            "CC": ["MultiplicationCompiled.v", "HelperFenvWF.v"],
        },
        "Exponentiation": {
            "Core": ["Exponentiation.v","ExpWrappers.v"],
            "Tree": ["ExponentiationTreeCompiled.v"],
            "TreeC": ["ExponentiationTreeCorrect.v"],
            "CC": ["ExponentiationCompiled.v"],
        },
        # "Series Helper": {
        #     "Core": ["Multiplication.v", "Exponentiation.v","MultWrappers.v", "ExpWrappers.v"],
        #     "Tree": ["MultiplicationTreeCompiled.v", "ExponentiationTreeCompiled.v",],
        #     "CC": ["MultiplicationCompiled.v", "ExponentiationCompiled.v", "SeriesHelperCompilation.v", "HelperFenvWF.v"]
        #     # "rsa_impLang.v",
        # },
        "Series": {
            "Core": ["SeriesExample.v", "SeriesExampleProofInputs.v"],
            "Tree": ["SeriesExampleTreeProofCompiled.v"],
            "TreeC": ["SeriesExampleTreeCorrect.v"],
            "CC": ["SeriesExampleProofCompiled.v","SeriesExampleProofCompiledOther.v",],
        },
        "Square Root": {
            "Core": ["SquareRootCore.v",],
            "Tree": ["SquareRootTreeCompiled.v"],
            "TreeC": ["SquareRootTreeCorrect.v"],
            "CC": ["SquareRoot.v"],
        }
            
    },
    "Automation": ["Imp_LangTrickTactics.v","MiscTactics.v","SemanTactics.v","ZArithTactics.v","TerminatesForSure.v","ReflectionMachinery.v","LogicPropHints.v","Imp_LangLogicHelpers.v","AimpWfAndCheckProofAuto.v","NotTerribleBImpLangInversion.v","ImpHasVariableReflection.v",
                   "FunctionWellFormedReflection.v",
                   "ProofCompAuto.v","ProofCompAutoAnother.v", "StackFrameReflection.v","StackPurestBaseReflection.v","StateUpdateReflection.v"],
    "Ignore": ["rsa_impLang.v","Adequacy.v","BloomFilterArrayProgram.v","HelperWrappers.v","PrimeFactors.v","ProofCompExamples.v"],
    "Other": []
}

def flip_dict(d):
    flipped = {}
    for k in d:
        if isinstance(d[k], list):
            for v in d[k]:
                flipped[v] = [k]
                pass
            pass
        elif isinstance(d[k], dict):
            flipped_child = flip_dict(d[k])
            for k1, v1 in flipped_child.items():
                flipped[k1] = [k] + v1
                pass
            pass
        pass
    return flipped
                
def assign_to_dict(d, val, *keys):
    if len(keys) == 1:
        
        if keys[0] in d:
            d[keys[0]].append(val)
            pass
        else:
            d[keys[0]] = [val]
        pass
    elif len(keys) > 1:
        if keys[0] not in d:
            d[keys[0]] = {}
        assign_to_dict(d[keys[0]], val, *keys[1:])
        pass
    pass

def recurse_over_dict(d, f, *keys):
    if isinstance(d, list):
        f(keys, d)
        pass
    elif isinstance(d, dict):
        for k,v in d.items():
            recurse_over_dict(v, f, *(list(keys) + [k]))
            pass
        pass
    pass

workdir = os.path.dirname(os.path.realpath(__file__))
def get_wc(wc_dict):
    def get_wc_helper(keys, files):
        if not files:
            return
        coqwc_output = subprocess.run(['coqwc'] + files,check=True, stdout=subprocess.PIPE, universal_newlines=True)

        specs = 0
        thms = 0
        for f in files:
            specs_grep = subprocess.run([os.path.join(workdir, "bin", "count_specs.sh"), f], universal_newlines=True, stdout=subprocess.PIPE)
            lemmas_grep = subprocess.run([os.path.join(workdir, "bin", "count_lemmas.sh"), f], universal_newlines=True, stdout=subprocess.PIPE)
            output = specs_grep.stdout
            specs += int(output.strip())
            thms += int(lemmas_grep.stdout.strip())
            pass
        # print(keys)
        coqwc = coqwc_output.stdout.split("\n")
        total = [s for s in re.split(r"\s+", coqwc[-2]) if s]
        loc = 0
        if len(total) == 4:
            spec_loc = int(total[0])
            proof_loc = int(total[1])
            loc = int(total[0]) + int(total[1])
            loc_obj = {
                "LOC": loc,
                "Spec": specs,
                "Theorems": thms
            }
            if prints_proof_loc:
                loc_obj["Proof LOC"] = proof_loc
                pass
            if prints_spec_loc:
                loc_obj["Spec LOC"] = spec_loc
                pass
            assign_to_dict(wc_dict, loc_obj,
                           *keys)
            # print(loc)
            # print("Specs:", specs)
            # print("Theorems:", thms)
            pass
        pass
    return get_wc_helper



def get_index_order():
    index = ["loc"]
    if prints_proof_loc:
        index.append("proof loc")
        pass
    if prints_spec_loc:
        index.append("spec loc")
        pass
    index.append("theorems")
    index.append("specs")
    return index

def setup_lines(headers_lines, numbers_lines, max_cats, index_order, args):
    for i in range(max_cats):
        headers_lines.append([])
        pass

    for i in index_order:
        numbers_lines[i] = []
        pass

    if args.index:
        for l in headers_lines:
            l.append("")
            pass
        for i in index_order:
            numbers_lines[i].append(i)
            pass
        pass
    pass
    

def add_lines_recursive_version(max_cats, columns_order, args, line_counts
                                ):
    headers_lines = []
    numbers_lines = {}
    index_order = get_index_order()
    if args.verbose:
        print("Max cats: ", max_cats, file=sys.stderr)
    setup_lines(headers_lines, numbers_lines, max_cats, index_order, args)
    # for i in range(max_cats):
    #     headers_lines.append([])
    
    # for i in index_order:
    #     numbers_lines[i] = []
    #     pass

    # if args.index:
    #     for l in headers_lines:
    #         l.append("")
    #         pass
    #     for i in index_order:
    #         numbers_lines[i].append(i)
    #         pass
    #     pass
    def add_loc_obj(loc_obj):
        numbers_lines["loc"].append(loc_obj["LOC"])
        numbers_lines["specs"].append(loc_obj["Spec"])
        numbers_lines["theorems"].append(loc_obj["Theorems"])
        if prints_proof_loc:
            numbers_lines["proof loc"].append(loc_obj["Proof LOC"])
            pass
        if prints_spec_loc:
            numbers_lines["spec loc"].append(loc_obj["Spec LOC"])
            pass
        pass
    def inner_columns_order(keys):
        skeys = sorted(filter(lambda x: x not in args.omit, keys) if args.omit else keys)
        if args.verbose:
            print(skeys, file=sys.stderr)
            pass
        if skeys == ["Lang", "Logic", "WF"]:
            return skeys
        elif skeys == ["CC", "Core", "Tree"]:
            return ["Core", "Tree", "CC"]
        elif skeys == ["CC", "Core", "Tree", "TreeC"]:
            return ["Core", "Tree", "TreeC", "CC"]
        elif skeys == ["Exponentiation", "Multiplication", "Series", "Square Root"]:
            return ["Multiplication", "Exponentiation", "Series", "Square Root"]
        elif skeys == ["Code", "Spec", "\\flowA", "\\flowB"]:
            return ["Code", "Spec", "\\flowB", "\\flowA"]
        return keys
    def add_lines(k, line_counts_dict, header_index=0):
        num_added = 0
        if args.omit and k in args.omit:
            return 0
        if isinstance(line_counts_dict[k], dict):
            
            added = 0
            for k1 in inner_columns_order(list(line_counts_dict[k].keys())):
                added += add_lines(k1, line_counts_dict[k], header_index=header_index + 1)
                pass
            num_added += added
            if args.amp:
                headers_lines[header_index].append("\multicolumn{" + str(added) + "}{c|}{" + k + "}")
                pass
            else:
                # print(k, header_index, len(headers_lines))
                headers_lines[header_index].append(k)
                pass
            if added > 1:
                headers_lines[header_index] += [""] * (added - 1)
                pass
            if added == 0:
                headers_lines[header_index] = headers_lines[header_index][:-1]
            pass
        elif isinstance(line_counts_dict[k], list):
            loc_obj = line_counts_dict[k][0]
            if not args.amp and k == "Other":
                for i in range(len(headers_lines) - 1):
                    headers_lines[i].append("")
                    pass
                # headers_lines[0].append("")
                headers_lines[-1].append(k)
                pass
            else:
                headers_lines[header_index].append(k)
                for i in range(header_index + 1, len(headers_lines)):
                    headers_lines[i].append("")
                    pass
                pass
            add_loc_obj(loc_obj)
            num_added += 1
        return num_added

    
    
    for c in columns_order:
        if c in line_counts:
            add_lines(c, line_counts, header_index=0)
            pass
        pass
    return headers_lines, numbers_lines


def filter_header_line(line, args):
    skip_next_n = 0
    filtered_line = []
    for l in line:
        if skip_next_n > 0:
            skip_next_n -= 1
            continue
        else:
            matched = re.match(r"\\multicolumn\{([^}]+)\}\{([^}]+)\}\{([^}]+)\}", l)
            if matched:
                num = int(matched.group(1))
                col = matched.group(2)
                header = matched.group(3)
                skip_next_n = num - 1
                if args.amp and header in ["Imp", "Stack"]:
                    l = "\\multicolumn{" + str(num) + "}{" + col + "}{" + "\\" + header + "}"
                    pass
                pass
            if matched and args.space_nicely:
                filtered_line.append(l + ("\t" * 2 * skip_next_n))
                pass
            else:
                if args.amp and l == "Automation":
                    filtered_line.append("\\multirow{2}{*}{Auto}")
                    pass
                elif args.amp and l == "Instantiations":
                    filtered_line.append("\\multirow{2}{*}{Insts.}")
                    pass
                elif args.amp and l == "Other":
                    filtered_line.append("\\multirow{2}{*}{Other}")
                else:
                    filtered_line.append(l)
                    pass
                    
                pass
            pass
        pass
    return filtered_line

def set_globals(args):
    global prints_proof_loc
    global prints_per_file
    global prints_spec_loc
    global has_max_level

    prints_proof_loc = args.proof_loc
    prints_spec_loc = args.spec_loc
    prints_per_file = args.per_file
    if args.max_level > 0:
        has_max_level = True
    if args.split_loc:
        prints_spec_loc = True
        prints_proof_loc = True
        pass
    pass

def xor(a, b):
    return (a and not b) or (not a and b)

def check_for_args_errors(args):
    # Rule out incomprehensible situations
    if args.expand and args.collapse and any(c in args.expand for c in args.collapse):
        inter = [c for c in args.collapse if c in args.expand]
        print(f"ERROR: --collapse and --expand options should be disjoint: {args.collapse} and {args.expand} both contain {inter}", file=sys.stderr)
        exit(1)
        pass
    if args.verbose and args.split_loc and xor(args.proof_loc, args.spec_loc):
        print(f"NOTICE: --split-loc entails --proof-loc AND --spec-loc ", file=sys.stderr)
        pass
    if args.verbose and not args.amp and args.space_nicely:
        print(f"NOTICE: --amp not set but --space-nicely given --- --space-nicely does nothing without --amp", file=sys.stderr)
        pass
    if args.expand and args.omit and any(e in args.omit for e in args.expand):
        inter = [o for o in args.expand if o in args.omit]
        print(f"WARNING: --omit supersedes --expand, will ignore expanded categories {inter}", file=sys.stderr)
    if args.other and args.per_file:
        print(f"WARNING: --other supersedes the option --per-file", file=sys.stderr)
        pass
    if args.other and "Other" in args.expand:
        print(f"WARNING: --other supersedes `--expand Other`", file=sys.stderr)
        pass
    if args.output == "csv":
        print(f"WARNING: --output csv is not yet supported", file=sys.stderr)
    pass


def get_up_to_key(lst, keywords):
    if len(lst) > 0:
        if lst[0] in keywords:
            return [lst[0]]
        return [lst[0]] + get_up_to_key(lst[1:], keywords)
        pass
    return lst

if __name__ == "__main__":

    Imp_LangTrick = os.path.join(workdir, "Imp_LangTrick")
    plugin = os.path.join(workdir, "plugin")
    
    files_to_cats = flip_dict(default_files_sep)
    args = get_args()
    check_for_args_errors(args)
    set_globals(args)
    files = []
    if not args.files:
        files = [f for f in glob.glob(os.path.join(Imp_LangTrick, "**/*.v"), recursive=True)] + [f for f in glob.glob(os.path.join(plugin, "src/*.ml"), recursive=True)]
        pass
    else:
        files = args.files
        pass
    # print(args.cat)
    # print(files_to_cats)
    max_cats = 0

    
    

    cats_to_full_filenames = {}
    # {"Other": []}
    for f in files:
        # print(f)
        bn = os.path.basename(f)
        if not args.include_ml and bn.endswith(".ml"):
            continue
        if bn in files_to_cats and (not args.cat or files_to_cats[bn][0] in args.cat):
            keys = files_to_cats[bn]
            if args.collapse and any(k in args.collapse for k in keys):
                keys = get_up_to_key(keys, args.collapse)
            if args.verbose:
                print(keys, file=sys.stderr)
                pass
            if (not (args.collapse and any(k in args.collapse for k in keys)) and prints_per_file) or (args.expand and any(k in args.expand for k in keys)):
                keys += [bn]
                pass
            max_cats = max(max_cats, len(keys))
            assign_to_dict(cats_to_full_filenames, f, *keys)
            pass
        elif not args.cat:
            if not args.other:
                if ((prints_per_file and (args.collapse and "Other" not in args.collapse)) or ( args.expand and "Other" in args.expand)):
                    if args.verbose:
                        print("Does 1", file=sys.stderr)
                        pass
                    if "Other" not in cats_to_full_filenames:
                        cats_to_full_filenames["Other"] = {}
                        pass
                    cats_to_full_filenames["Other"][bn] = [f]
                    max_cats = max(max_cats, 2)
                    pass
                else:
                    if args.verbose:
                        print("Does 2", file=sys.stderr)
                        pass
                    if "Other" not in cats_to_full_filenames:
                        cats_to_full_filenames["Other"] = []
                        pass
                    cats_to_full_filenames["Other"].append(f)
                    pass
            else:
                if args.verbose:
                    print("Does 3", file=sys.stderr)
                    pass
                if "Other" not in cats_to_full_filenames:
                    cats_to_full_filenames["Other"] = []
                    pass
                cats_to_full_filenames["Other"].append(f)
                pass
            pass
        pass

    if args.other:
        print("\n".join(cats_to_full_filenames["Other"]))
        pass
    else:
        # print(cats_to_full_filenames)
        line_counts = {}
        # print(cats_to_full_filenames)
        recurse_over_dict(cats_to_full_filenames, get_wc(line_counts))

        columns_order = ["Imp", "Stack", "Base", "Compiler", "Instantiations", "Unverified Proof Compiler", "Examples", "Automation", "Other"]
        header1_line = []
        header2_line = []
        headers_lines = []
        if args.verbose:
            print("INFO: Max header line depth: ", max_cats, file=sys.stderr)
        for i in range(max_cats):
            headers_lines.append([])
            pass
        
        index_order = get_index_order()
        numbers_lines = {}
        for i in index_order:
            numbers_lines[i] = []
            pass
        
        headers_lines1, numbers_lines1 = add_lines_recursive_version(max_cats, columns_order, args, line_counts)
        
        joiner = "\t&\t" if args.amp else "\t"
        
        
        for line in headers_lines1:
            # print(line)
            if args.amp:
                filtered = filter_header_line(line, args)
                if args.verbose:
                    print("INFO: Header line:", filtered, file=sys.stderr)
                print(joiner.join(filtered))
                pass
            else:
                print(joiner.join(line))
            pass
        
        for i in index_order:
            print(joiner.join(list(map(str, numbers_lines1[i]))))
            pass
        pass
    pass

    
        
