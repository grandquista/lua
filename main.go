package main

import (
	"fmt"
	"os"
)

// A FileSet represents a set of source files. Methods of file sets are synchronized; multiple goroutines may invoke them concurrently.
type FileSet struct{}

type parseError struct{}

func (err parseError) Error() string {
	return "Lua parse error."
}

// ParseDir calls ParseFile for all files with names ending in ".lua" in the directory specified by path and returns a map of package name -> package AST with all the packages found.
//
// If filter != nil, only the files with os.FileInfo entries passing through the filter (and ending in ".lua") are considered. The mode bits are passed to ParseFile unchanged. Position information is recorded in fset, which must not be nil.
//
// If the directory couldn't be read, a nil map and the respective error are returned. If a parse error occurred, a non-nil but incomplete map and the first error encountered are returned.
func ParseDir(fset *FileSet, path string, filter func(os.FileInfo) bool, mode Mode) (pkgs map[string]*Package, first error) {
	return nil, parseError{}
}

// ParseExpr is a convenience function for obtaining the AST of an expression x. The position information recorded in the AST is undefined. The filename used in error messages is the empty string.
func ParseExpr(x string) (Expr, error) {
	return nil, parseError{}
}

// ParseExprFrom is a convenience function for parsing an expression. The arguments have the same meaning as for ParseFile, but the source must be a valid Lua (type or value) expression. Specifically, fset must not be nil.
func ParseExprFrom(fset *FileSet, filename string, src interface{}, mode Mode) (Expr, error) {
	return nil, parseError{}
}

// ParseFile parses the source code of a single Lua source file and returns the corresponding File node. The source code may be provided via the filename of the source file, or via the src parameter.
//
// If src != nil, ParseFile parses the source from src and the filename is only used when recording position information. The type of the argument for the src parameter must be string, []byte, or io.Reader. If src == nil, ParseFile parses the file specified by filename.
//
// The mode parameter controls the amount of source text parsed and other optional parser functionality. Position information is recorded in the file set fset, which must not be nil.
//
// If the source couldn't be read, the returned AST is nil and the error indicates the specific failure. If the source was read but syntax errors were found, the result is a partial AST (with Bad* nodes representing the fragments of erroneous source code). Multiple errors are returned via a scanner.ErrorList which is sorted by file position.
func ParseFile(fset *FileSet, filename string, src interface{}, mode Mode) (f *File, err error) {
	return nil, parseError{}
}

// A Mode value is a set of flags (or 0). They control the amount of source code parsed and other optional parser functionality.
type Mode uint

// Mode flags.
const (
	PackageClauseOnly Mode = 1 << iota // stop parsing after package clause
	ImportsOnly                        // stop parsing after import declarations
	ParseComments                      // parse comments and add them to AST
	Trace                              // print a trace of parsed productions
	DeclarationErrors                  // report declaration errors
	AllErrors                          // report all errors (not just the first 10 on different lines)
)

// ParseError error.
type ParseError error

// File ast.
type File Chunk

// Package ast.
type Package Chunk

// Expr ast.
type Expr Exp

// Args main.
type Args interface{}

// Chunk main.
type Chunk struct {
	Block
}

// Block main.
type Block struct {
	stats []Stat
	*RetStat
}

// Elipsis main.
type Elipsis struct{}

// Exp main.
type Exp interface{}

// ExpList main.
type ExpList struct {
	exps []Exp
}

// False main.
type False struct{}

// FuncName main.
type FuncName struct {
	names  []Name
	method *Name
}

// FuncBody main.
type FuncBody struct{}

// FunctionCall main.
type FunctionCall struct {
	PrefixExp
	*Name
	Args
}

// FunctionDef main.
type FunctionDef struct{ FuncBody }

// Index main.
type Index struct {
	PrefixExp
	Exp
}

// Label main.
type Label struct {
	Name
}

// LiteralString main.
type LiteralString struct{}

// Name main.
type Name struct{}

// NameList main.
type NameList struct {
	names []Name
}

// Nil main.
type Nil struct{}

// Numeral main.
type Numeral struct {
	float64
}

// PrefixExp main.
type PrefixExp interface{}

// Property main.
type Property struct {
	PrefixExp
	Name
}

// RetStat main.
type RetStat struct {
	*ExpList
}

// Semi main.
type Semi struct{}

// Stat main.
type Stat interface{}

// StringLiteral main.
type StringLiteral interface{}

// TableConstructor main.
type TableConstructor struct{}

// True main.
type True struct{}

// UnExp main.
type UnExp struct {
	UnOp
	Exp
}

// UnOp main.
type UnOp interface{}

// Var main.
type Var interface{}

// VarList main.
type VarList struct {
	exps []Var
}

// Parser main.
type Parser struct {
	data string
}

func (parser Parser) chunk(i int) (Chunk, int) {
	block, i := parser.block(i)
	return Chunk{block}, i
}

func (parser Parser) block(i int) (Block, int) {
	s := make([]Stat, 0)
	stat, i := parser.stat(i)
	for stat != nil {
		s = append(s, stat)
		stat, i = parser.stat(i)
	}
	retstat, i := parser.retstat(i)
	return Block{s, retstat}, i
}

func (parser Parser) stat(i int) (Stat, int) {
	if parser.data[i] == ';' {
		return Semi{}, parser.white(i)
	}
	return Semi{}, parser.white(i)
}

func (parser Parser) retstat(i int) (*RetStat, int) {
	if parser.data[i:i+6] == "return" {
		explist, j := parser.explist(parser.white(i + 6))
		if parser.data[j] == ';' {
			j = parser.white(j + 1)
		}
		return &RetStat{explist}, j
	}
	return nil, i
}

func (parser Parser) label(i int) (*Label, int) {
	if parser.data[i:i+2] == "::" {
		name, j := parser.name(parser.white(i + 2))
		if name != nil && parser.data[j:j+2] == "::" {
			return &Label{*name}, parser.white(j + 2)
		}
		panic(parseError{})
	}
	return nil, i
}

func (parser Parser) funcname(i int) (*FuncName, int) {
	n := make([]Name, 1)
	name, i := parser.name(i)
	if name == nil {
		return nil, i
	}
	n = append(n, *name)
	for parser.data[i] == '.' {
		name, j := parser.name(parser.white(i + 1))
		if name == nil {
			panic(parseError{})
		}
		i = j
		n = append(n, *name)
	}
	if parser.data[i] == ':' {
		name, j := parser.name(parser.white(i + 1))
		if name != nil {
			return &FuncName{n, name}, j
		}
		panic(parseError{})
	}
	return &FuncName{n, nil}, i
}

func (parser Parser) varlist(i int) (*VarList, int) {
	l := make([]Var, 1)
	v, i := parser.vari(i)
	if v == nil {
		return nil, i
	}
	l = append(l, v)
	for parser.data[i] == ',' {
		v, j := parser.vari(parser.white(i + 1))
		if v == nil {
			panic(parseError{})
		}
		i = j
		l = append(l, v)
	}
	return &VarList{l}, i
}

func (parser Parser) vari(i int) (Var, int) {
	name, i := parser.name(i)
	if name != nil {
		return name, i
	}
	prefixexp, j := parser.prefixexp(i)
	if parser.data[j] == '[' {
		exp, k := parser.exp(parser.white(j + 1))
		if exp != nil && parser.data[k] == ']' {
			return Index{prefixexp, exp}, parser.white(k + 1)
		}
		panic(parseError{})
	}
	if parser.data[j] == '.' {
		name, k := parser.name(parser.white(j + 1))
		if name != nil {
			return Property{prefixexp, *name}, k
		}
		panic(parseError{})
	}
	return nil, i
}

func (parser Parser) namelist(i int) (*NameList, int) {
	n := make([]Name, 1)
	name, i := parser.name(i)
	if name == nil {
		return nil, i
	}
	n = append(n, *name)
	for parser.data[i] == ',' {
		name, j := parser.name(parser.white(i + 1))
		if name == nil {
			panic(parseError{})
		}
		i = j
		n = append(n, *name)
	}
	return &NameList{n}, i
}

func (parser Parser) explist(i int) (*ExpList, int) {
	exps := make([]Exp, 1)
	exp, i := parser.exp(i)
	if exp == nil {
		return nil, i
	}
	exps = append(exps, exp)
	for parser.data[i] == ',' {
		exp, j := parser.exp(parser.white(i + 1))
		if exp == nil {
			panic(parseError{})
		}
		i = j
		exps = append(exps, exp)
	}
	return &ExpList{exps}, i
}

func (parser Parser) exp(i int) (Exp, int) {
	if parser.data[i:i+3] == "nil" {
		return Nil{}, parser.white(i + 3)
	}
	if parser.data[i:i+5] == "false" {
		return False{}, parser.white(i + 5)
	}
	if parser.data[i:i+4] == "true" {
		return True{}, parser.white(i + 4)
	}
	var num float64
	n, err := fmt.Sscanf(parser.data[i:], "%f", &num)
	if err == nil {
		return Numeral{num}, i + n
	}
	literalstring, i := parser.literalstring(i)
	if literalstring != nil {
		return literalstring, i
	}
	if parser.data[i:i+3] == "..." {
		return Elipsis{}, parser.white(i + 3)
	}
	functiondef, i := parser.functiondef(i)
	if functiondef != nil {
		return functiondef, i
	}
	prefixexp, i := parser.prefixexp(i)
	if prefixexp != nil {
		return prefixexp, i
	}
	tableconstructor, i := parser.tableconstructor(i)
	if tableconstructor != nil {
		return tableconstructor, i
	}
	unop, j := parser.unop(i)
	if unop != nil {
		exp, k := parser.exp(j)
		return UnExp{unop, exp}, k
	}
	return nil, i
}

func (parser Parser) prefixexp(i int) (PrefixExp, int) {
	vari, i := parser.vari(i)
	if vari != nil {
		return vari, i
	}
	functioncall, i := parser.functioncall(i)
	if functioncall != nil {
		return functioncall, i
	}
	if parser.data[i] == '(' {
		exp, j := parser.exp(parser.white(i))
		if exp != nil && parser.data[j] == ')' {
			return exp, parser.white(j + 1)
		}
	}
	return nil, i
}

func (parser Parser) functioncall(i int) (*FunctionCall, int) {
	prefixexp, j := parser.prefixexp(i)
	if prefixexp != nil {
		if parser.data[j] == ':' {
			name, k := parser.name(parser.white(j + 1))
			if name != nil {
				args, l := parser.args(k)
				if args != nil {
					return &FunctionCall{prefixexp, name, args}, l
				}
			}
			panic(parseError{})
		} else {
			args, k := parser.args(j)
			if args != nil {
				return &FunctionCall{prefixexp, nil, args}, k
			}
		}
	}
	return nil, i
}

func (parser Parser) args(i int) (Args, int) {
	if parser.data[i] == '(' {
		explist, j := parser.explist(parser.white(i + 1))
		if parser.data[j] == ')' {
			return explist, j
		}
		panic(parseError{})
	}
	tableconstructor, j := parser.tableconstructor(i)
	if tableconstructor != nil {
		return tableconstructor, j
	}
	stringliteral, j := parser.stringliteral(i)
	return stringliteral, j
}

func (parser Parser) functiondef(i int) (*FunctionDef, int) {
	if parser.data[i:i+8] == "function" {
		funcbody, j := parser.funcbody(parser.white(i + 8))
		if funcbody != nil {
			return &FunctionDef{*funcbody}, j
		}
		panic(parseError{})
	}
	return nil, i
}

func (parser Parser) funcbody(i int) (*FuncBody, int) {
	return nil, i
}

func (parser Parser) tableconstructor(i int) (*TableConstructor, int) {
	return nil, i
}

func (parser Parser) unop(i int) (UnOp, int) {
	return nil, i
}

func (parser Parser) literalstring(i int) (*LiteralString, int) {
	return nil, i
}

func (parser Parser) name(i int) (*Name, int) {
	return nil, i
}

func (parser Parser) stringliteral(i int) (*StringLiteral, int) {
	return nil, i
}

func (parser Parser) white(i int) int {
	set := " \n\r"
	data := parser.data[i]
	for i := range set {
		if data == set[i] {
			return parser.white(i + 1)
		}
	}
	return i
}

func main() {}
