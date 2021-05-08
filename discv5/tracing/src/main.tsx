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
import {SentWhoAreYouPackets} from "./SentWhoAreYouPackets";
import React, {ReactElement} from "react";
import {ArwesThemeProvider, FrameBox, StylesBaseline, Text, TextProps} from "@arwes/core";
import {FONT_FAMILY_CODE, FONT_FAMILY_ROOT} from "./index";
import {Animator, AnimatorGeneralProvider} from "@arwes/animation";

// Workaround for the compile error:
// TS2339: Property 'showOpenFilePicker' does not exist on type 'Window & typeof globalThis'.
declare global { interface Window { showOpenFilePicker: any; } }

export const SCALE = 100;
export const DISTANCE_BETWEEN_NODES = 1000;
export const TIME_PROGRESS_PER_STEP = 1; // milli
export const IDLE_STEPS = 5;

const _scene = new THREE.Scene();
_scene.background = new THREE.Color(0x021114);
const _logs = new Logs();
const _nodes: Map<string, Node> = new Map();
const _nodeIds: Array<string> = [];
const _sentMessages = new SentMessages();
const _sentWhoAreYou = new SentWhoAreYouPackets();

// ///////////////////////////////////////
// Camera
//
// Three.jsではカメラを作成し、その視点から見えるものがレンダラーを介してcanvasへ描画される
// https://ics.media/entry/14771/images/concept.png
// ///////////////////////////////////////
// new THREE.PerspectiveCamera(画角, アスペクト比, 描画開始距離, 描画終了距離)
const _camera = new THREE.PerspectiveCamera(
    45,
    window.innerWidth / window.innerHeight,
    1,
    5000 * SCALE
);
_camera.position.set(0, 0, 2000);

let _canvas: HTMLCanvasElement | null = null;

type TracingProps = {
  tracing: boolean;
}

export class Tracing extends React.Component<TracingProps> {
  state = {
    showPanel: false,
    panelContents: <Text></Text>,
  }

  mouse = new THREE.Vector2();
  raycaster = new THREE.Raycaster();
  objectHighlighter = new ObjectHighlighter(_scene);


  constructor(props: TracingProps) {
    super(props);

    this.handleMouseMove = this.handleMouseMove.bind(this);
  }

  handleMouseMove(event: React.MouseEvent) {
    if (_canvas === null) {
      return;
    }
    // canvas要素上のXY座標
    const x = event.clientX - _canvas.offsetLeft;
    const y = event.clientY - _canvas.offsetTop;
    // canvas要素の幅・高さ
    const w = _canvas.offsetWidth;
    const h = _canvas.offsetHeight;

    // -1〜+1の範囲で現在のマウス座標を登録する
    this.mouse.x = ( x / w ) * 2 - 1;
    this.mouse.y = -( y / h ) * 2 + 1;

    // レイキャスト = マウス位置からまっすぐに伸びる光線ベクトルを生成
    this.raycaster.setFromCamera(this.mouse, _camera);
    // その光線とぶつかったオブジェクトを得る
    const intersects = this.raycaster.intersectObjects(_scene.children);
    const highlightedObject = this.objectHighlighter.highlight(intersects);

    let showPanel = false;
    let panelContents = <Text></Text>;
    if (highlightedObject && highlightedObject.userData.panelContents) {
      showPanel = true;
      panelContents = highlightedObject.userData.panelContents;
    }

    this.setState({
      showPanel: showPanel,
      panelContents: panelContents,
    });
  }

  onCanvasLoaded = (canvas: HTMLCanvasElement) => {
    _canvas = canvas;
  }

  render() {
    const display = this.props.tracing ? 'block' : 'none';
    return (
        <div>
          <canvas
              id="tracing"
              style={{display: display}}
              onMouseMove={this.handleMouseMove}
              ref={this.onCanvasLoaded}
          />
          <Panel show={this.state.showPanel} contents={this.state.panelContents} />
        </div>
    )
  }
}

const panelAnimator = { duration: { enter: 10, exit: 100 } };

type PanelProps = {
  show: boolean;
  contents: ReactElement;
}

const Panel = (props: PanelProps) => {
  let activate = props.show;
  return (
      <div
          style={{
            position: "absolute",
            left: "3%",
            bottom: "3%",
            zIndex: 100,
            textAlign: "left",
          }}
      >
        <ArwesThemeProvider>
          <StylesBaseline styles={{
            'html, body': { fontFamily: FONT_FAMILY_ROOT },
            'code, pre': { fontFamily: FONT_FAMILY_CODE },
            'body': { textAlign: "center" }
          }} />
          <AnimatorGeneralProvider animator={panelAnimator}>
            <Animator animator={{ activate, manager: 'stagger' }}>
              <FrameBox>
                {props.contents}
              </FrameBox>
            </Animator>
          </AnimatorGeneralProvider>
        </ArwesThemeProvider>
      </div>
  );
};

export async function openFilePicker() {
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

  const file = await handle.getFile();
  const ab = await file.arrayBuffer();
  const bytes = new Uint8Array(ab);

  const reason = tracing.Log.verify(bytes);
  if (reason != null) {
    console.error(reason);
    alert(reason);
    return;
  }

  return handle;
}

export async function bootstrap(handle: any /*FileSystemFileHandle*/) {
  console.dir(handle);
  const file = await handle.getFile();
  const ab = await file.arrayBuffer();
  const bytes = new Uint8Array(ab);
  const reader = Reader.create(bytes);

  try {
    while (true) {
      // http://protobufjs.github.io/protobuf.js/Type.html#decodeDelimited
      const log = tracing.Log.decodeDelimited(reader);
      _logs.add(log);

      if (log.event === 'start' && log.start && log.start.nodeId) {
        _nodeIds.push(log.start.nodeId);
      }
    }
  } catch (e) {
    if (e instanceof RangeError) {
      console.debug("Decoding the logs has done successfully.");
    } else {
      throw e;
    }
  }

  _logs.sort();

  start();
}

function start() {
  const _globals = new Globals(_logs, _nodeIds, _nodes);

  const width = window.innerWidth;
  const height = window.innerHeight;


  // ///////////////////////////////////////
  // Stats
  // https://github.com/mrdoob/stats.js
  // ///////////////////////////////////////
  const stats = Stats();
  stats.showPanel(0); // 0: fps, 1: ms, 2: mb, 3+: custom
  stats.domElement.style.position = 'absolute';
  stats.domElement.style.left = '8px';
  stats.domElement.style.top = '8px';
  document.body.appendChild(stats.dom);

  // ///////////////////////////////////////
  // Renderer
  // ///////////////////////////////////////
  if (_canvas === null) {
    throw new Error("_canvas is null");
  }
  const renderer = new THREE.WebGLRenderer({
    canvas: _canvas,
  });

  // デフォルトではレンダラーのサイズが小さいため、setSize()メソッドでサイズを設定
  renderer.setSize(width, height);

  // スマホでも綺麗に見えるように、デバイスピクセル比も設定
  // これを設定しないとスマホだとぼやけてしまう
  renderer.setPixelRatio(window.devicePixelRatio);

  // TrackballControls
  // https://threejs.org/docs/#examples/en/controls/TrackballControls
  const controls = new TrackballControls(_camera, renderer.domElement);

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
  if (_logs.first_key === null) {
    throw new Error('Logs has not been initialized.');
  }
  let time = LogKeyHelper.decrease(_logs.first_key, IDLE_STEPS * TIME_PROGRESS_PER_STEP);

  // ///////////////////////////////////////
  // Node
  // ///////////////////////////////////////
  for (let i = 0; i < _nodeIds.length; i++) {
    const node = new Node(_scene, _globals, _nodeIds[i]);
    _nodes.set(node.id, node);
    console.info("Node: " + node.id);
  }

  animate();

  function animate() {
    requestAnimationFrame(animate);
    advanceTrace();

    controls.update();
    stats.begin();
    renderer.render(_scene, _camera);
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

    // console.info(`step: ${step}, time: ${time}, logs: ${logs.length}`);

    logs.forEach((log: tracing.Log) => {
      // console.info(log);
      processLog(log, step);
    });

    step += 1;
    time = LogKeyHelper.increase(time, TIME_PROGRESS_PER_STEP);
  }
}

// grow existing nodes along the time axis
// https://threejs.org/docs/#manual/en/introduction/How-to-update-things
function growExistingNodes(step: number): void {
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
    case 'sendWhoareyou':
      processWhoareyou(log, step);
      break;
    case 'sendHandshakeMessage':
      processHandshakeMessage(log, step);
      break;
    case 'handleMessage':
      processHandleMessage(log, step);
      break;
    case 'handleWhoareyou':
      processHandleWhoareyou(log, step);
      break;
    default:
      console.error("unknown event", log);
  }
}

function processStart(log: tracing.Log, step: number) {
  const node = _nodes.get(log.start.nodeId);
  node.start(step);
}

function processShutdown(log, step) {
  const node = _nodes.get(log.shutdown.nodeId);
  node.shutdown(step);
}

function protoToMessage(sender: Node, recipient: Node, message): Message {
  switch (message.message) {
    case 'ping':
      return new Ping(
          sender,
          recipient,
          message.ping.requestId,
          message.ping.enrSeq
      );
    case 'pong':
      return new Pong(
          sender,
          recipient,
          message.pong.requestId,
          message.pong.enrSeq,
          message.pong.recipientIp,
          message.pong.recipientPort
      );
    case 'findNode':
      return new Findnode(
          sender,
          recipient,
          message.findNode.requestId,
          message.findNode.distances
      );
    case 'nodes':
      return new Nodes(
          sender,
          recipient,
          message.nodes.requestId,
          message.nodes.total,
          message.nodes.nodes
      );
    case 'random':
      return new Random(
          sender,
          recipient
      );
    default:
      console.error("unknown message type", message);
      break;
  }
}

function processOrdinaryMessage(log: tracing.Log, step: number) {
  const event = log.sendOrdinaryMessage;
  const sender = _nodes.get(event.sender);
  const recipient = _nodes.get(event.recipient);
  const message = protoToMessage(sender, recipient, log.sendOrdinaryMessage);

  if (event.random !== null) {
    // Due to Random packet has no request_id, we can't trace when the Random packet has been handled by the recipient.
    // So we can only draw an arrow which grows horizontally towards recipient.
    sender.drawMessageHorizontally(recipient, step, message);
  } else {
    _sentMessages.addOrdinaryMessage(
        sender.id,
        recipient.id,
        message,
        step
    );
  }
}

function processHandleMessage(log: tracing.Log, step: number): void {
  const event = log.handleMessage;
  const sender = _nodes.get(event.sender);
  const recipient = _nodes.get(event.recipient);
  const message = protoToMessage(sender, recipient, event);

  const sentMessage = _sentMessages.take(sender.id, recipient.id, message.requestId());
  sender.drawMessage(recipient, step, sentMessage);
}

function processWhoareyou(log, step) {
  const sender = _nodes.get(log.sendWhoareyou.sender);
  const recipient = _nodes.get(log.sendWhoareyou.recipient);
  _sentWhoAreYou.add(
      sender.id,
      recipient.id,
      log.sendWhoareyou.idNonce,
      log.sendWhoareyou.enrSeq,
      step
  );
}

function processHandleWhoareyou(log: tracing.Log, step: number): void {
  const event = log.handleWhoareyou;
  const sender = _nodes.get(event.sender);
  const recipient = _nodes.get(event.recipient);

  const sentWhoAreYou = _sentWhoAreYou.take(sender.id, recipient.id, event.enrSeq);
  sender.drawWhoAreYou(recipient, step, sentWhoAreYou);
}

function processHandshakeMessage(log, step) {
  const sender = _nodes.get(log.sendHandshakeMessage.sender);
  const recipient = _nodes.get(log.sendHandshakeMessage.recipient);
  const message = protoToMessage(sender, recipient, log.sendHandshakeMessage);

  _sentMessages.addHandshakeMessage(
      sender.id,
      recipient.id,
      message,
      step
  );
}
