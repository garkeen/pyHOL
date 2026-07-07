<template>
  <div class="integral-container">
    <!-- Menu -->
    <nav class="navbar navbar-light bg-info">
      <div class="container-fluid">
        <span class="navbar-brand" @click="loadBookList" style="cursor:pointer">Integral</span>
        <div class="navbar-nav flex-row flex-wrap">
          <div class="nav-item dropdown">
            <a class="nav-link dropdown-toggle" href="#" role="button" data-bs-toggle="dropdown">Proof</a>
            <ul class="dropdown-menu">
              <li><a class="dropdown-item" href="#" @click.prevent="clearItem">Clear</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="applyRule('FullSimplify')">Simplify</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="addFuncDef">Add definition</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="addGoal">Add goal</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="proofByCalculation">Proof by calculation</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="proofByInduction">Proof by induction</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="proofByRewriteGoal">Proof by rewrite goal</a></li>
            </ul>
          </div>
          <div class="nav-item dropdown">
            <a class="nav-link dropdown-toggle" href="#" role="button" data-bs-toggle="dropdown">Limits</a>
            <ul class="dropdown-menu">
              <li><a class="dropdown-item" href="#" @click.prevent="applyRule('LHopital')">L'Hopital Rule</a></li>
            </ul>
          </div>
          <div class="nav-item dropdown">
            <a class="nav-link dropdown-toggle" href="#" role="button" data-bs-toggle="dropdown">Series</a>
            <ul class="dropdown-menu">
              <li><a class="dropdown-item" href="#" @click.prevent="applySeriesExpansion">Series expansion</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="applyRule('SeriesEvaluationIdentity')">Series evaluation</a></li>
            </ul>
          </div>
          <div class="nav-item dropdown">
            <a class="nav-link dropdown-toggle" href="#" role="button" data-bs-toggle="dropdown">Integral</a>
            <ul class="dropdown-menu">
              <li><a class="dropdown-item" href="#" @click.prevent="applyRule('IndefiniteIntegralIdentity')">Indefinite integral identity</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="applyRule('ReplaceSubstitution')">Replace substitution</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="applyRule('DefiniteIntegralIdentity')">Definite integral identity</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="forwardSubstitution">Forward substitution</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="backwardSubstitution">Backward substitution</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="integrateByParts">Integrate by parts</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="applyRule('ElimInfInterval')">Improper integral to limit</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="applyRule('DerivIntExchange')">Exchange deriv and integral</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="applyRule('IntSumExchange')">Exchange sum and integral</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="splitRegion">Splitting an Integral</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="solveEquation">Solve equation</a></li>
            </ul>
          </div>
          <div class="nav-item dropdown">
            <a class="nav-link dropdown-toggle" href="#" role="button" data-bs-toggle="dropdown">Rewrite</a>
            <ul class="dropdown-menu">
              <li><a class="dropdown-item" href="#" @click.prevent="rewriteEquation">Rewriting</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="expandDefinition">Expand definition</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="foldDefinition">Fold definition</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="applyExpandPolynomial">Expand polynomial</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="rewriteUsingIdentity">Apply identity</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="applyTheorem">Apply lemma</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="applyRule('ApplyInductHyp')">Apply inductive hyp</a></li>
            </ul>
          </div>
          <div class="nav-item dropdown">
            <a class="nav-link dropdown-toggle" href="#" role="button" data-bs-toggle="dropdown">Equation</a>
            <ul class="dropdown-menu">
              <li><a class="dropdown-item" href="#" @click.prevent="variableSubstitution">Variable substitution</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="applyLimitBothSides">Take limit on both sides</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="applyDerivBothSides">Differentiate both sides</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="applyRule('IntegrateBothSide')">Integrate both sides</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="solveEquation2">Solve equation</a></li>
            </ul>
          </div>
        </div>
      </div>
    </nav>

    <!-- Main content -->
    <div class="main-content">
      <!-- Left panel: file browser -->
      <div class="left-panel">
        <div v-if="content_state === false" class="panel-section">
          <h6 class="panel-title">Books</h6>
          <div class="file-list">
            <div v-for="name in book_list" :key="name" class="file-item"
                 @click="openBook(name)">
              {{ name }}
            </div>
          </div>
        </div>
        <div v-if="content_state === true" class="panel-section">
          <h6 class="panel-title">Items</h6>
          <div class="file-list">
            <div v-for="(item, index) in content" :key="index" class="file-item"
                 :class="{active: cur_id === index}"
                 @click="initialize(index)">
              <div v-if="'type' in item && item.type === 'FuncDef'">
                <span class="math-text">Definition</span>
                <MathEquation :data="'\\(' + item.latex_eq + '\\)'"/>
              </div>
              <div v-if="'type' in item && item.type === 'Lemma'">
                <span class="math-text">Lemma</span>
                <MathEquation :data="'\\(' + item.latex_eq + '\\)'"/>
              </div>
              <div v-if="'type' in item && item.type === 'Goal'">
                <span class="math-text">Goal</span>
                <MathEquation :data="'\\(' + item.latex_goal + '\\)'"/>
              </div>
              <div v-if="'type' in item && item.type === 'Calculation'">
                <span class="math-text">Calculate</span>
                <MathEquation :data="'\\(' + item.latex_start + '\\)'"/>
              </div>
            </div>
          </div>
        </div>
      </div>

      <!-- Center panel: proof/problem display -->
      <div class="center-panel">
        <div v-if="content.length > 0 && cur_id !== undefined">
          <div v-if="'type' in content[cur_id] && content[cur_id].type === 'FuncDef'">
            <FuncDef :item="content[cur_id]" :label="''"
                     :selected_item="selected_item"
                     :selected_facts="selected_facts"/>
          </div>
          <div v-if="'type' in content[cur_id] && content[cur_id].type === 'Lemma'">
            <Lemma :item="content[cur_id]" :label="''"
                   :selected_item="selected_item"
                   :selected_facts="selected_facts"/>
          </div>
          <div v-if="'type' in content[cur_id] && content[cur_id].type === 'Goal'">
            <Goal :item="content[cur_id]" :label="''"
                  @select="selectItem"
                  @select_fact="selectFact"
                  :selected_item="selected_item"
                  :selected_facts="selected_facts"/>
          </div>
          <div v-if="'type' in content[cur_id] && content[cur_id].type === 'Calculation'">
            <Calculation :item="content[cur_id]" :label="''"
                         @select="selectItem"
                         @select_fact="selectFact"
                         :selected_item="selected_item"
                         :selected_facts="selected_facts"/>
          </div>
        </div>
        <div v-if="content.length === 0">
          <div class="book-title">
            {{ book_content.name }}
          </div>
          <div v-for="(item, index) in book_content.content" :key="index">
            <div v-if="item.type === 'header'">
              <div v-if="item.level === 1" class="book-header1">
                {{ item.name }}
              </div>
              <div v-if="item.level === 2" class="book-header2">
                {{ item.name }}
              </div>
            </div>
            <div v-if="item.type === 'definition'">
              <MathEquation :data="'\\(' + item.latex_str + '\\)'" class="indented-text"
                            @click="openFile(item.path)" style="cursor:pointer"/>
            </div>
            <div v-if="item.type === 'problem'">
              <MathEquation :data="'\\(' + item.latex_str + '\\)'" class="indented-text"
                            @click="openFile(item.path)" style="cursor:pointer"/>
              <span v-if="'latex_conds' in item && item.latex_conds.length > 0">
                <span class="math-text indented-text">for &nbsp;</span>
                <span v-for="(cond, cidx) in item.latex_conds" :key="cidx">
                  <span v-if="cidx > 0">, &nbsp;</span>
                  <MathEquation :data="'\\(' + cond + '\\)'"/>
                </span>
              </span>
            </div>
            <div v-if="item.type === 'axiom'">
              <MathEquation :data="'\\(' + item.latex_str + '\\)'" class="indented-text"/>
              <span v-if="'latex_conds' in item && item.latex_conds.length > 0">
                <span class="math-text indented-text">for &nbsp;</span>
                <span v-for="(cond, cidx) in item.latex_conds" :key="cidx">
                  <span v-if="cidx > 0">, &nbsp;</span>
                  <MathEquation :data="'\\(' + cond + '\\)'"/>
                </span>
              </span>
            </div>
            <div v-if="item.type === 'table'" style="margin: 5px">
              <table style="border-collapse: collapse">
                <tbody>
                  <tr>
                    <td style="border-style: solid; padding: 3px">
                      <MathEquation :data="'\\(' + '{x}' + '\\)'"/>
                    </td>
                    <td v-for="(entry, eidx) in item.latex_table" :key="eidx"
                        style="border-style: solid; padding: 3px">
                      <MathEquation :data="'\\(' + entry.x + '\\)'"/>
                    </td>
                  </tr>
                  <tr>
                    <td style="border-style: solid; padding: 3px">
                      <MathEquation :data="'\\(' + item.funcexpr + '\\)'"/>
                    </td>
                    <td v-for="(entry, eidx) in item.latex_table" :key="eidx"
                        style="border-style: solid; padding: 3px">
                      <MathEquation :data="'\\(' + entry.y + '\\)'"/>
                    </td>
                  </tr>
                </tbody>
              </table>
            </div>
          </div>
        </div>
      </div>

      <!-- Right panel: dialog -->
      <div class="right-panel">
        <div v-if="r_query_mode === 'add definition'">
          <span class="math-text">Add function definition:</span><br/>
          <ExprQuery v-model="expr_query1"/><br/>
          <div v-for="(cond, index) in cond_query" :key="index">
            <ExprQuery :modelValue="cond" @update:modelValue="setCondQuery(index, $event)"/><br/>
          </div>
          <button class="btn btn-sm btn-primary" @click="doAddFuncDef">OK</button>&nbsp;
          <button class="btn btn-sm btn-secondary" @click="cond_query.push('')">Add condition</button>
        </div>
        <div v-if="r_query_mode === 'add goal'">
          <span class="math-text">Add goal:</span><br/>
          <ExprQuery v-model="expr_query1"/><br/>
          <div v-for="(cond, index) in cond_query" :key="index">
            <ExprQuery :modelValue="cond" @update:modelValue="setCondQuery(index, $event)"/><br/>
          </div>
          <button class="btn btn-sm btn-primary" @click="doAddGoal">OK</button>&nbsp;
          <button class="btn btn-sm btn-secondary" @click="cond_query.push('')">Add condition</button>
        </div>
        <div v-if="r_query_mode === 'apply induction'">
          <span class="math-text">Please specify induction variable</span><br/>
          <input v-model="induct_var" class="form-control form-control-sm" style="width:200px"><br/>
          <span class="math-text">starting from</span><br/>
          <ExprQuery v-model="expr_query1"/>
          <button class="btn btn-sm btn-primary" @click="doApplyInduction">OK</button>
        </div>
        <div v-if="r_query_mode === 'apply rewrite goal'">
          <div class="math-text">Select lemma to start from:</div>
          <div v-for="(item, index) in theorems" :key="index"
               @click="doApplyRewriteGoal(index)" style="cursor:pointer">
            <MathEquation :data="'\\(' + item.latex_eq + '\\)'"/>
          </div>
        </div>
        <div v-if="r_query_mode === 'integrate by parts'">
          <span class="math-text">Integrate by parts on: </span>
          <MathEquation :data="'\\(' + sep_int[0].latex_body + '\\)'"/><br/>
          <MathEquation data="Choose \(u\) and \(v\) such that \(u\cdot\mathrm{d}v\) is the integrand."/>
          <div>
            <MathEquation data="\(u=\)"/>
            <ExprQuery v-model="expr_query1"/>
          </div>
          <div>
            <MathEquation data="\(v=\)"/>
            <ExprQuery v-model="expr_query2"/><br/>
          </div>
          <button class="btn btn-sm btn-primary" @click="doIntegrateByParts">OK</button>
        </div>
        <div v-if="r_query_mode === 'forward substitution'">
          <MathEquation :data="'\\(' + sep_int[int_id].latex_expr + '\\)'"/><br/>
          <span class="math-text">Location: {{ sep_int[int_id].loc }}</span><br/>
          <button class="btn btn-sm btn-outline-secondary" :disabled="int_id === 0" @click="int_id--">prev</button>
          <button class="btn btn-sm btn-outline-secondary" :disabled="int_id === sep_int.length - 1" @click="int_id++">next</button><br/>
          <span class="math-text">Substitution on: </span>
          <MathEquation :data="'\\(' + sep_int[int_id].latex_body + '\\)'"/><br/>
          <span class="math-text">Substitute </span>
          <input v-model="subst_var" class="form-control form-control-sm" style="width:200px"><br/>
          <span class="math-text"> for</span><br/>
          <ExprQuery v-model="expr_query1"/><br/>
          <button class="btn btn-sm btn-primary" @click="doForwardSubstitution">OK</button>
        </div>
        <div v-if="r_query_mode === 'backward substitution'">
          <span class="math-text">Backward substitution on: </span>
          <MathEquation :data="'\\(' + sep_int[int_id].latex_body + '\\)'"/><br/>
          <span class="math-text">Location: {{ sep_int[int_id].loc }}</span><br/>
          <button class="btn btn-sm btn-outline-secondary" :disabled="int_id === 0" @click="int_id--">prev</button>
          <button class="btn btn-sm btn-outline-secondary" :disabled="int_id === sep_int.length - 1" @click="int_id++">next</button><br/>
          <span class="math-text">New variable </span>
          <input v-model="subst_var" class="form-control form-control-sm" style="width:200px"><br/>
          <span class="math-text">Substitute </span>
          <span class="math-text-italic">{{ sep_int[int_id].var_name }}</span>
          <span class="math-text"> for</span><br/>
          <ExprQuery v-model="expr_query1"/><br/>
          <button class="btn btn-sm btn-primary" @click="doBackwardSubstitution">OK</button>
        </div>
        <div v-if="r_query_mode === 'rewrite equation'">
          <div class="math-text">Select subexpression:</div>
          <input ref="select_expr1" :value="lastExpr"
                 class="form-control form-control-sm" style="width:500px" disabled="disabled"
                 @select="selectExpr"><br/>
          &nbsp;<MathEquation :data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/><br/>
          <span class="math-text">Rewrite subexpression to</span><br/>
          <ExprQuery v-model="expr_query1"/>
          <button class="btn btn-sm btn-primary" @click="doRewriteEquation">OK</button>
        </div>
        <div v-if="r_query_mode === 'rewrite using identity'">
          <div class="math-text">Select subexpression:</div>
          <input ref="select_expr1" :value="lastExpr"
                 class="form-control form-control-sm" style="width:500px" disabled="disabled"
                 @select="selectExprIdentity"><br/>
          &nbsp;<MathEquation :data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/><br/>
          <div v-for="(item, index) in identity_rewrites" :key="index">
            <MathEquation @click="applyIdentity(index)"
                          :data="'\\(=' + item.latex_res + '\\)'"
                          style="cursor:pointer"/>
          </div>
        </div>
        <div v-if="r_query_mode === 'split region'">
          <div class="math-text">Split region at:</div>
          <ExprQuery v-model="expr_query1"/>
          <button class="btn btn-sm btn-primary" @click="doSplitRegion">OK</button>
        </div>
        <div v-if="r_query_mode === 'select theorem'">
          <div class="math-text">Select subexpression:</div>
          <input ref="select_expr1" :value="lastExpr"
                 class="form-control form-control-sm" style="width:500px" disabled="disabled"
                 @select="selectExpr"><br/>
          &nbsp;<MathEquation :data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/><br/>
          <div class="math-text">Select theorem to apply:</div>
          <div v-for="(item, index) in theorems" :key="index"
               @click="doApplyTheorem(index)" style="cursor:pointer">
            <MathEquation :data="'\\(' + item.latex_eq + '\\)'"/>
          </div>
        </div>
        <div v-if="r_query_mode === 'query vars'">
          <div class="math-text">Enter instantiation in theorem</div>
          <div v-for="(item, index) in query_vars" :key="index">
            <MathEquation :data="'\\(' + item.var + '\\to \\)'"/>
            <ExprQuery v-model="item.expr"/>
          </div>
          <button class="btn btn-sm btn-primary" @click="doVariableSubstitution">OK</button>
        </div>
        <div v-if="r_query_mode === 'derivate both sides'">
          <span class="math-text">Please specify variable</span><br/>
          <input v-model="deriv_var" class="form-control form-control-sm" style="width:200px">
          <button class="btn btn-sm btn-primary" @click="doApplyDerivBothSides">OK</button>
        </div>
        <div v-if="r_query_mode === 'solve equation'">
          <div class="math-text">Select subexpression to solve for:</div>
          <input ref="select_expr1" :value="lastExpr"
                 class="form-control form-control-sm" style="width:500px" disabled="disabled"
                 @select="selectExpr"><br/>
          &nbsp;<MathEquation :data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/><br/>
          <button class="btn btn-sm btn-primary" @click="doSolveEquation">Solve</button>
        </div>
        <div v-if="r_query_mode === 'limit both sides'">
          <span class="math-text">Take limit as variable</span><br/>
          <input v-model="limit_var" class="form-control form-control-sm" style="width:200px">
          <span class="math-text">goes to</span><br/>
          <ExprQuery v-model="expr_query1"/>
          <button class="btn btn-sm btn-primary" @click="doApplyLimitBothSides">OK</button>
        </div>
        <div v-if="r_query_mode === 'series expansion'">
          <div class="math-text">Series expansion on:</div>
          <input ref="select_expr1" :value="lastExpr"
                 class="form-control form-control-sm" style="width:500px" disabled="disabled"
                 @select="selectExpr"><br/>
          &nbsp;<MathEquation :data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/><br/>
          <span class="math-text">Index variable</span><br/>
          <input v-model="index_var" class="form-control form-control-sm" style="width:200px">
          <button class="btn btn-sm btn-primary" @click="doApplySeriesExpansion">OK</button>
        </div>
        <div v-if="r_query_mode === 'expand polynomial'">
          <div class="math-text">Expand polynomial on:</div>
          <input ref="select_expr1" :value="lastExpr"
                 class="form-control form-control-sm" style="width:500px" disabled="disabled"
                 @select="selectExpr"><br/>
          &nbsp;<MathEquation :data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/><br/>
          <button class="btn btn-sm btn-primary" @click="doApplyExpandPolynomial">OK</button>
        </div>
        <div v-if="r_query_mode === 'expand definition'">
          <div class="math-text">Expand definition on:</div>
          <div v-for="(item, index) in def_choices" :key="index"
               @click="doExpandDefinition(index)" style="cursor:pointer">
            <MathEquation :data="'\\(' + item.latex_subexpr + '\\)'"/>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup>
import { ref, computed, onMounted } from 'vue'
import api from '../api'
import MathEquation from '../components/util/MathEquation.vue'
import FuncDef from '../components/integral/FuncDef.vue'
import ExprQuery from '../components/integral/ExprQuery.vue'
import Goal from '../components/integral/Goal.vue'
import Lemma from '../components/integral/Lemma.vue'
import Calculation from '../components/integral/Calculation.vue'

// Display list of books (false) or list of items in a file
const content_state = ref(undefined)

// List of integral books
const book_list = ref([])
// Currently open book
const book_name = ref('interesting')
// Content of the currently opened book
const book_content = ref({})

// Currently opened file
const filename = ref(undefined)
// List of problems in the file
const content = ref([])
// ID of the selected item
const cur_id = ref(undefined)

// Current query mode
const r_query_mode = ref(undefined)

// All separate integrals
const sep_int = ref([])

// List of choices for fold/unfold definition
const def_choices = ref([])

// Selected goal
const selected_item = ref(undefined)

// Query for expressions
const expr_query1 = ref(undefined)
const expr_query2 = ref(undefined)

// Query for conditions
const cond_query = ref([])

// Query for substitution variable
const subst_var = ref(undefined)

// Query for induction variable
const induct_var = ref(undefined)

// Query for variable to differentiate
const deriv_var = ref(undefined)

// Query for limit variable
const limit_var = ref(undefined)

// Query for index variable
const index_var = ref('n')

// Selected fact
const selected_facts = ref({})

// Selected latex expression
const selected_expr = ref(undefined)
const latex_selected_expr = ref(undefined)
const selected_loc = ref(undefined)

// List of identity rewrites for selected expression
const identity_rewrites = ref([])

// List of theorems
const theorems = ref(undefined)

// Query for variable instantiation
const query_vars = ref(undefined)

// Expression in the chosen step
const last_expr = ref(undefined)

// The index of sep-integrals
const int_id = ref(0)

// Template ref
const select_expr1 = ref(null)

const lastExpr = computed(() => {
  if (content.value.length > 0 && cur_id.value !== undefined) {
    query_last_expr()
    return last_expr.value
  } else {
    return ''
  }
})

const loadBookList = async () => {
  const response = await api.post('/integral-load-book-list')
  book_list.value = response.data.book_list
  content_state.value = false
  content.value = []
  cur_id.value = undefined
}

const loadBookContent = async () => {
  const data = { bookname: book_name.value }
  const response = await api.post('/integral-load-book-content', data)
  book_content.value = response.data
}

const openBook = async (name) => {
  book_name.value = name
  loadBookContent()
}

const query_last_expr = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value
  }
  try {
    const response = await api.post('/query-last-expr', data)
    if (response.data.status === 'ok') {
      last_expr.value = response.data.last_expr
    } else {
      last_expr.value = ''
    }
  } catch (err) {
    last_expr.value = ''
  }
}

const openFile = async (fname) => {
  const data = { filename: fname }
  filename.value = fname
  const response = await api.post('/integral-open-file', data)
  content.value = response.data.content
  cur_id.value = undefined
  content_state.value = true
}

const initialize = async (index) => {
  r_query_mode.value = undefined
  cur_id.value = index
  selected_item.value = undefined
  selected_facts.value = {}
}

const selectItem = (item_id) => {
  selected_item.value = item_id
  r_query_mode.value = undefined
}

const selectFact = (item_id) => {
  if (item_id in selected_facts.value) {
    delete selected_facts.value[item_id]
  } else {
    selected_facts.value[item_id] = true
  }
}

const clearItem = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value === undefined ? '' : selected_item.value
  }
  const response = await api.post('/clear-item', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    if ('selected_item' in response.data) {
      selected_item.value = response.data.selected_item
    }
  }
}

const setCondQuery = (index, value) => {
  cond_query.value[index] = value
}

const addFuncDef = () => {
  r_query_mode.value = 'add definition'
}

const doAddFuncDef = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    eq: expr_query1.value,
    conds: cond_query.value
  }
  const response = await api.post('/add-function-definition', data)
  if (response.data.status === 'ok') {
    content.value = response.data.state
    cur_id.value = content.value.length - 1
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
    expr_query1.value = ''
    cond_query.value = []
  }
}

const addGoal = () => {
  r_query_mode.value = 'add goal'
}

const doAddGoal = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    goal: expr_query1.value,
    conds: cond_query.value
  }
  const response = await api.post('/add-goal', data)
  if (response.data.status === 'ok') {
    content.value = response.data.state
    cur_id.value = content.value.length - 1
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
    expr_query1.value = ''
    cond_query.value = []
  }
}

const proofByCalculation = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value
  }
  const response = await api.post('/proof-by-calculation', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
  }
}

const proofByInduction = () => {
  expr_query1.value = '0'
  r_query_mode.value = 'apply induction'
}

const doApplyInduction = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    induct_var: induct_var.value,
    start: expr_query1.value
  }
  const response = await api.post('/proof-by-induction', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
  }
}

const proofByRewriteGoal = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value
  }
  const response = await api.post('/query-theorems', data)
  if (response.data.status === 'ok') {
    theorems.value = response.data.theorems
    r_query_mode.value = 'apply rewrite goal'
  }
}

const doApplyRewriteGoal = async (index) => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    begin: theorems.value[index].eq
  }
  const response = await api.post('/proof-by-rewrite-goal', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
  }
}

const applyRule = async (rulename) => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: { name: rulename }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
  }
}

const expandDefinition = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value
  }
  const response = await api.post('/expand-definition', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
  } else if (response.data.status === 'choose') {
    def_choices.value = response.data.choices
    r_query_mode.value = 'expand definition'
  }
}

const doExpandDefinition = async (index) => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'ExpandDefinition',
      func_name: def_choices.value[index].func_name,
      loc: def_choices.value[index].loc
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

const foldDefinition = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value
  }
  const response = await api.post('/fold-definition', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
  }
}

const integrateByParts = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value
  }
  const response = await api.post('/query-integral', data)
  if (response.data.status === 'ok') {
    sep_int.value = response.data.integrals
    r_query_mode.value = 'integrate by parts'
  }
}

const doIntegrateByParts = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'IntegrationByParts',
      u: expr_query1.value,
      v: expr_query2.value
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

const forwardSubstitution = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value
  }
  const response = await api.post('/query-integral', data)
  if (response.data.status === 'ok') {
    sep_int.value = response.data.integrals
    r_query_mode.value = 'forward substitution'
  }
}

const doForwardSubstitution = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'Substitution',
      var_name: subst_var.value,
      var_subst: expr_query1.value,
      loc: sep_int.value[int_id.value].loc
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

const backwardSubstitution = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value
  }
  const response = await api.post('/query-integral', data)
  if (response.data.status === 'ok') {
    sep_int.value = response.data.integrals
    int_id.value = 0
    r_query_mode.value = 'backward substitution'
  }
}

const doBackwardSubstitution = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'SubstitutionInverse',
      var_name: subst_var.value,
      var_subst: expr_query1.value,
      loc: sep_int.value[int_id.value].loc
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

const solveEquation = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    selected_facts: selected_facts.value
  }
  const response = await api.post('/solve-equation', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
    selected_facts.value = {}
  }
}

const rewriteEquation = () => {
  selected_expr.value = undefined
  latex_selected_expr.value = undefined
  r_query_mode.value = 'rewrite equation'
}

const selectExpr = async () => {
  if (!select_expr1.value) return
  const start = select_expr1.value.selectionStart
  const end = select_expr1.value.selectionEnd
  selected_expr.value = lastExpr.value.slice(start, end)
  const data = {
    expr: lastExpr.value,
    selected_expr: selected_expr.value
  }
  const response = await api.post('/query-latex-expr', data)
  if (response.data.status === 'ok') {
    latex_selected_expr.value = response.data.latex_expr
    selected_loc.value = response.data.loc
  }
}

const doRewriteEquation = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'Equation',
      old_expr: selected_expr.value,
      new_expr: expr_query1.value
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

const rewriteUsingIdentity = () => {
  selected_expr.value = undefined
  latex_selected_expr.value = undefined
  identity_rewrites.value = []
  r_query_mode.value = 'rewrite using identity'
}

const selectExprIdentity = async () => {
  if (!select_expr1.value) return
  const start = select_expr1.value.selectionStart
  const end = select_expr1.value.selectionEnd
  selected_expr.value = lastExpr.value.slice(start, end)
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    expr: selected_expr.value
  }
  const response = await api.post('/query-identities', data)
  if (response.data.status === 'ok') {
    latex_selected_expr.value = response.data.latex_expr
    identity_rewrites.value = response.data.results
  }
}

const applyIdentity = async (index) => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'ApplyIdentity',
      source: selected_expr.value,
      target: identity_rewrites.value[index].res
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

const splitRegion = () => {
  r_query_mode.value = 'split region'
}

const doSplitRegion = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'SplitRegion',
      c: expr_query1.value
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

const applyTheorem = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value
  }
  const response = await api.post('/query-theorems', data)
  if (response.data.status === 'ok') {
    theorems.value = response.data.theorems
    selected_expr.value = undefined
    latex_selected_expr.value = undefined
    r_query_mode.value = 'select theorem'
  }
}

const doApplyTheorem = async (index) => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'ApplyEquation',
      eq: theorems.value[index].eq,
      loc: selected_loc.value
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

const variableSubstitution = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value
  }
  const response = await api.post('/query-vars', data)
  if (response.data.status === 'ok') {
    query_vars.value = response.data.query_vars
    r_query_mode.value = 'query vars'
  }
}

const doVariableSubstitution = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'VarSubsOfEquation',
      subst: query_vars.value
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

const applyDerivBothSides = () => {
  r_query_mode.value = 'derivate both sides'
}

const doApplyDerivBothSides = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'DerivEquation',
      var: deriv_var.value
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

const solveEquation2 = () => {
  selected_expr.value = undefined
  latex_selected_expr.value = undefined
  r_query_mode.value = 'solve equation'
}

const doSolveEquation = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'SolveEquation',
      solve_for: selected_expr.value
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

const applyLimitBothSides = () => {
  r_query_mode.value = 'limit both sides'
}

const doApplyLimitBothSides = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'LimitEquation',
      var: limit_var.value,
      lim: expr_query1.value
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

const applySeriesExpansion = () => {
  selected_expr.value = undefined
  latex_selected_expr.value = undefined
  r_query_mode.value = 'series expansion'
}

const doApplySeriesExpansion = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'SeriesExpansionIdentity',
      old_expr: selected_expr.value,
      index_var: index_var.value
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

const applyExpandPolynomial = () => {
  r_query_mode.value = 'expand polynomial'
}

const doApplyExpandPolynomial = async () => {
  const data = {
    book: book_name.value,
    file: filename.value,
    content: content.value,
    cur_id: cur_id.value,
    selected_item: selected_item.value,
    rule: {
      name: 'ExpandPolynomial',
      loc: selected_loc.value
    }
  }
  const response = await api.post('/perform-step', data)
  if (response.data.status === 'ok') {
    content.value[cur_id.value] = response.data.item
    selected_item.value = response.data.selected_item
    r_query_mode.value = undefined
  }
}

onMounted(() => {
  loadBookList()
  book_name.value = 'interesting'
  loadBookContent()
})
</script>

<style scoped>
.integral-container {
  height: 100vh;
  display: flex;
  flex-direction: column;
  overflow: hidden;
}

.main-content {
  flex: 1;
  display: flex;
  overflow: hidden;
}

.left-panel {
  width: 250px;
  min-width: 250px;
  border-right: 1px solid #dee2e6;
  overflow-y: auto;
  background: #f8f9fa;
}

.center-panel {
  flex: 1;
  overflow-y: auto;
  padding: 15px;
}

.right-panel {
  width: 300px;
  min-width: 300px;
  border-left: 1px solid #dee2e6;
  overflow-y: auto;
  background: #f8f9fa;
  padding: 15px;
}

.panel-section {
  padding: 10px;
  border-bottom: 1px solid #dee2e6;
}

.panel-title {
  font-weight: bold;
  color: #495057;
  margin-bottom: 10px;
  padding-bottom: 5px;
  border-bottom: 2px solid #007bff;
}

.file-list {
  max-height: calc(100vh - 120px);
  overflow-y: auto;
}

.file-item {
  padding: 8px 12px;
  cursor: pointer;
  border-radius: 4px;
  margin-bottom: 2px;
}

.file-item:hover {
  background: #e9ecef;
}

.file-item.active {
  background: #007bff;
  color: white;
}

.book-title {
  text-align: center;
}

.book-header1 {
  font-size: x-large;
  font-weight: 500;
}

.book-header2 {
  font-size: large;
  font-weight: 500;
}

.selected {
  background-color: #cce5ff;
}

.selected-fact {
  background-color: #d4edda;
}
</style>
