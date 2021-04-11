import * as THREE from 'three';
import { tracing } from './generated/proto';
import {Random, Ping, Findnode, Nodes, Pong, Message} from './Message';
import { ObjectHighlighter } from "./ObjectHighlighter";
import { LogKeyHelper } from "./LogKeyHelper";
import { TrackballControls } from 'three/examples/jsm/controls/TrackballControls';
import Stats from 'three/examples/jsm/libs/stats.module';
import { Reader } from "protobufjs";
import { Globals } from './Globals';
import { Node } from "./Node";
import {Logs} from "./Logs";
import {SentMessages} from "./SentMessages";

// Workaround for the compile error:
// TS2339: Property 'showOpenFilePicker' does not exist on type 'Window & typeof globalThis'.
declare global { interface Window { showOpenFilePicker: any; } }

export const SCALE = 100;
export const DISTANCE_BETWEEN_NODES = 1000;
export const TIME_PROGRESS_PER_STEP = 1; // milli
export const IDLE_STEPS = 5;

const _scene = new THREE.Scene();
const _logs = new Logs();
const _nodes: Map<string, Node> = new Map();
const _nodeIds: Array<string> = [];
const _sentMessages = new SentMessages();
const _canvas: HTMLElement = document.querySelector<HTMLElement>("#tracing");
// マウス座標管理用のベクトル
const _mouse = new THREE.Vector2();
_canvas.addEventListener('mousemove', function (event: MouseEvent) {
  // canvas要素上のXY座標
  const x = event.clientX - this.offsetLeft;
  const y = event.clientY - this.offsetTop;
  // canvas要素の幅・高さ
  const w = this.offsetWidth;
  const h = this.offsetHeight;

  // -1〜+1の範囲で現在のマウス座標を登録する
  _mouse.x = ( x / w ) * 2 - 1;
  _mouse.y = -( y / h ) * 2 + 1;
});


(function () {
  const b: HTMLElement = document.getElementById('b');
  b.addEventListener('click', async () => {
    // https://developer.mozilla.org/en-US/docs/Web/API/Window/showOpenFilePicker
    // https://wicg.github.io/file-system-access/#api-showopenfilepicker
    const [handle] = await window.showOpenFilePicker({
      multiple: false,
      types: [
        {
          description: 'trace file',
          accept: {
            'text/plain': ['.log']
          },
        }
      ]
    });

    b.style.display = 'none';

    const file = await handle.getFile();
    const ab = await file.arrayBuffer();
    const bytes = new Uint8Array(ab);
    const reader = Reader.create(bytes);

    const reason = tracing.Log.verify(bytes);
    if (reason != null) {
      console.log(reason);
      alert(reason);
      return;
    }

    try {
      while (true) {
        // http://protobufjs.github.io/protobuf.js/Type.html#decodeDelimited
        const log = tracing.Log.decodeDelimited(reader);
        _logs.add(log);

        if (log.event === 'start') {
          _nodeIds.push(log.start.nodeId);
          // console.dir(log.start);
        }
        // console.dir(log);
        // console.dir(log.event);
      }
    } catch (e) {
      if (e instanceof RangeError) {
        // console.log("decoding has done");
      } else {
        throw e;
      }
    }

    _logs.sort();

    bootstrap();
  });
})();

function bootstrap() {
  const _globals = new Globals(_logs, _nodeIds, _nodes);

  const width = window.innerWidth;
  const height = window.innerHeight;


  // ///////////////////////////////////////
  // Stats
  // https://github.com/mrdoob/stats.js
  // ///////////////////////////////////////
  const stats = new Stats();
  stats.showPanel(0); // 0: fps, 1: ms, 2: mb, 3+: custom
  stats.domElement.style.position = 'absolute';
  stats.domElement.style.left = '8px';
  stats.domElement.style.top = '8px';
  document.body.appendChild(stats.dom);

  // ///////////////////////////////////////
  // Renderer
  // ///////////////////////////////////////
  const renderer = new THREE.WebGLRenderer({
    canvas: document.querySelector("#tracing")
  });

  // デフォルトではレンダラーのサイズが小さいため、setSize()メソッドでサイズを設定
  renderer.setSize(width, height);

  // スマホでも綺麗に見えるように、デバイスピクセル比も設定
  // これを設定しないとスマホだとぼやけてしまう
  renderer.setPixelRatio(window.devicePixelRatio);

  // ///////////////////////////////////////
  // Camera
  //
  // Three.jsではカメラを作成し、その視点から見えるものがレンダラーを介してcanvasへ描画される
  // https://ics.media/entry/14771/images/concept.png
  // ///////////////////////////////////////
  // new THREE.PerspectiveCamera(画角, アスペクト比, 描画開始距離, 描画終了距離)
  const camera = new THREE.PerspectiveCamera(
    45,
    width / height,
    1,
    5000 * SCALE
  );
  camera.position.set(0, 0, 2000);

  // TrackballControls
  // https://threejs.org/docs/#examples/en/controls/TrackballControls
  const controls = new TrackballControls(camera, renderer.domElement);

  // ///////////////////////////////////////
  // 5. ライトを作る
  // ///////////////////////////////////////
  // このままでは真っ暗なのでライトを作成する
  // DirectionalLight: 平行光源を意味します。平行光源は太陽光のように一定方向から差し込む光。
  // new THREE.DirectionalLight(色)
  const light = new THREE.DirectionalLight(0xffffff);
  light.intensity = 2; // 光の強さを倍に
  //  光源が斜めから差し込むようにライトの位置を変更しておく
  light.position.set(1, 1, 1);
  // ライトもシーンに追加することで反映される
  _scene.add(light);

  // ///////////////////////////////////////
  // animate
  // ///////////////////////////////////////
  let step: number = 0;
  // NOTE: `time` is a string value which consists of seconds and nanos.
  let time = LogKeyHelper.decrease(_logs.first_key, IDLE_STEPS * TIME_PROGRESS_PER_STEP);

  // ///////////////////////////////////////
  // Node
  // ///////////////////////////////////////
  for (let i = 0; i < _nodeIds.length; i++) {
    const node = new Node(_scene, _globals, _nodeIds[i]);
    _nodes.set(node.id, node);
    console.info("Node: " + node.id);
  }

  const objectHighlighter = new ObjectHighlighter(_scene);

  const raycaster = new THREE.Raycaster();

  animate();

  function animate() {
    requestAnimationFrame(animate);
    advanceTrace();

    // レイキャスト = マウス位置からまっすぐに伸びる光線ベクトルを生成
    raycaster.setFromCamera(_mouse, camera);
    // その光線とぶつかったオブジェクトを得る
    const intersects = raycaster.intersectObjects(_scene.children);
    objectHighlighter.highlight(intersects);

    controls.update();
    stats.begin();
    renderer.render(_scene, camera);
    stats.end();
  }

  function advanceTrace() {
    if (step >= _globals.max_step) {
      return;
    }

    growExistingNodes(step);

    const logs = _logs.slice(
        time,
        TIME_PROGRESS_PER_STEP
    );

    console.info(`step: ${step}, time: ${time}, logs: ${logs.length}`);

    logs.forEach((log: tracing.Log) => {
      console.info(log);
      processLog(log, step);
    });

    step += 1;
    time = LogKeyHelper.increase(time, TIME_PROGRESS_PER_STEP);
  }
}

// grow existing nodes along the time axis
// https://threejs.org/docs/#manual/en/introduction/How-to-update-things
function growExistingNodes(step) {
  for (const [k, node] of _nodes.entries()) {
    const line = node.line;
    line.geometry.setDrawRange(0, step);
    line.geometry.attributes.position.needsUpdate = true; // required after the first render
  }
}

function processLog(log: tracing.Log, step: number) {
  switch (log.event) {
    case 'start':
      processStart(log, step);
      break;
    case 'shutdown':
      processShutdown(log, step);
      break;
    case 'sendOrdinaryMessage':
      processOrdinaryMessage(log, step);
      break;
    case 'handleOrdinaryMessage':
      processHandleOrdinaryMessage(log, step);
      break;
    case 'sendWhoareyou':
      processWhoareyou(log, step);
      break;
    case 'sendHandshakeMessage':
      processHandshakeMessage(log, step);
      break;
    default:
      console.error("unknown event", log);
  }
}

function processStart(log, step) {
  const node = _nodes.get(log.start.nodeId);
  node.start(step);
}

function processShutdown(log, step) {
  const node = _nodes.get(log.shutdown.nodeId);
  node.shutdown(step);
}

function protoToMessage(message): Message {
  switch (message.message) {
    case 'ping':
      return new Ping(message.ping.requestId, message.ping.enrSeq);
    case 'pong':
      return new Pong(message.pong.requestId, message.pong.enrSeq, message.pong.recipientIp, message.pong.recipientPort);
    case 'findNode':
      return new Findnode(message.findNode.requestId, message.findNode.distances);
    case 'nodes':
      return new Nodes(message.nodes.requestId, message.nodes.total, message.nodes.nodes);
    case 'random':
      return new Random();
    default:
      console.error("unknown message type", message);
      break;
  }
}

function processOrdinaryMessage(log: tracing.Log, step: number) {
  const ordinaryMessage = log.sendOrdinaryMessage;
  const sender = _nodes.get(ordinaryMessage.sender);
  const recipient = _nodes.get(ordinaryMessage.recipient);
  const message = protoToMessage(log.sendOrdinaryMessage);

  if (ordinaryMessage.random !== null) {
    // Due to Random packet has no request_id, we can't trace when the Random packet has been handled by the recipient.
    // So we can only draw an arrow which grows horizontally towards recipient.
    sender.drawOrdinaryMessageHorizontally(recipient, step, message);
  } else {
    _sentMessages.add(
        sender.id,
        recipient.id,
        message,
        step
    );
  }
}

function processHandleOrdinaryMessage(log: tracing.Log, step: number): void {
  const ordinaryMessage = log.handleOrdinaryMessage;
  const sender = _nodes.get(ordinaryMessage.sender);
  const recipient = _nodes.get(ordinaryMessage.recipient);
  const message = protoToMessage(ordinaryMessage);

  // FIXME
  try {
    const sentMessage = _sentMessages.take(sender.id, recipient.id, message.requestId());
    sender.drawOrdinaryMessage(recipient, step, sentMessage);
  } catch (e) {
    console.error(e);
  }
}

function processWhoareyou(log, step) {
  const sender = _nodes.get(log.sendWhoareyou.sender);
  const recipient = _nodes.get(log.sendWhoareyou.recipient);
  sender.sendWhoAreYou(
      recipient,
      step,
      log.sendWhoareyou.idNonce,
      log.sendWhoareyou.enrSeq
  );
}

function processHandshakeMessage(log, step) {
  const sender = _nodes.get(log.sendHandshakeMessage.sender);
  const recipient = _nodes.get(log.sendHandshakeMessage.recipient);
  const message = protoToMessage(log.sendHandshakeMessage);
  sender.sendHandshakeMessage(
      recipient,
      step,
      message
  );
}
