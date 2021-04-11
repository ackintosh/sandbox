import { IDLE_STEPS, TIME_PROGRESS_PER_STEP } from './main';
import { LogKeyHelper } from "./LogKeyHelper";
import {Node} from "./Node";
import {Logs} from "./Logs";

export class Globals {
  readonly logs: Logs;
  readonly nodeIds: Array<string>;
  readonly nodes: Map<string, Node>;
  readonly max_step: number;

  constructor(logs: Logs, nodeIds: Array<string>, nodes: Map<string, Node>) {
    this.logs = logs;
    this.nodeIds = nodeIds;
    this.nodes = nodes;
    this.max_step = this.calculateMaxStep();
  }

  private calculateMaxStep() {
    let steps = LogKeyHelper.subtract(this.logs.last_key, this.logs.first_key) / TIME_PROGRESS_PER_STEP;
    return steps + (IDLE_STEPS * 2);
  }
}
