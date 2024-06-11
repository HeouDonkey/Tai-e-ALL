/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.List;
import java.util.Optional;

import static java.lang.System.in;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }


    /**
     * 外部会调用这个方法（具体是哪里我还没看源码，也不知道，应该是lib里面调用的。）
     *
     * @param cfg 传入了控制流图
     * @return 返回setfact（这里我理解的就是边界in和out里面数据流的那个因素列表）
     */
    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        return new SetFact<>();//去看SetFact源码，初始化为空。
    }

    @Override
    public SetFact<Var> newInitialFact() {
        return new SetFact<>();
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        target.union(fact);
    }

    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        //In[b] = use[b] union (out[b] - defb)
        Optional<LValue> def = stmt.getDef();
        List<RValue> uses = stmt.getUses();

        SetFact<Var> tmp = new SetFact<>();



        //tmp = out[b]-defb
        tmp.set(out);
        if (def.isPresent()
                && def.get() instanceof Var
                && tmp.contains((Var) (def.get()))
                // && !uses.contains(def.get())
        )
        {
            tmp.remove((Var) (def.get()));
        }
        //use[b] union tmp
        for (RValue use : uses) {
            if (use instanceof Var) {
                tmp.add((Var) use);
            }
        }
        //如果in 和out相同
        if (tmp.equals(in)) return false;
        in.set(tmp);
        return true;
    }
}
