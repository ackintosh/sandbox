import * as THREE from 'three';
import {Globals} from "./Globals";
import {DISTANCE_BETWEEN_NODES, SCALE} from "./main";
import {SentMessage} from "./SentMessages";

const COLOR_NODE_ID = 0xffffff;
const COLOR_START = 0xffddff;
const COLOR_SHUTDOWN = 0xffddff;
const COLOR_WHOAREYOU = 0x00dd00;
const FONT = new THREE.Font(require('three/examples/fonts/helvetiker_regular.typeface.json'));

export class NodePos {
    readonly x: number;
    readonly y: number;
    readonly z: number;

    constructor(x: number, y: number, z: number) {
        this.x = x;
        this.y = y;
        this.z = z;
    }
}

export class Node {
    readonly scene: THREE.Scene;
    readonly globals: Globals;
    id: string;
    pos: NodePos;
    line: THREE.Line;

    private calculateNodePos(): NodePos {
        const angle = 360 / this.globals.nodeIds.length * this.globals.nodes.size;
        const x = Math.cos(angle * Math.PI / 180) * DISTANCE_BETWEEN_NODES;
        const z = Math.sin(angle * Math.PI / 180) * DISTANCE_BETWEEN_NODES;

        return new NodePos(x, 0, z);
    }

    constructor(scene: THREE.Scene, globals: Globals, id: string) {
        this.scene = scene;
        this.globals = globals;
        this.id = id;
        this.pos = this.calculateNodePos();

        this.showLine();
        this.showNodeId();
    }

    // create new line
    // https://threejs.org/docs/index.html#manual/en/introduction/Drawing-lines
    showLine() {
        // geometry
        const geometry = new THREE.BufferGeometry();

        // attributes
        const positions = new Float32Array( this.globals.max_step * 3 ); // 3 vertices per point

        let y, yIndex, xIndex, zIndex;
        y = yIndex = xIndex = zIndex = 0;
        for (let i = 0; i < this.globals.max_step; i ++) {
            xIndex = (i * 3);
            yIndex = (i * 3) + 1;
            zIndex = (i * 3) + 2;
            positions[xIndex] = this.pos.x;
            positions[yIndex] = y;
            positions[zIndex] = this.pos.z;
            y = (-1 * SCALE) * i;
        }

        geometry.setAttribute( 'position', new THREE.BufferAttribute( positions, 3 ) );

        // draw range
        const drawCount = 2; // draw the first 2 points, only
        geometry.setDrawRange( 0, drawCount );

        // create a blue LineBasicMaterial
        const material = new THREE.LineBasicMaterial( { color: 0xff0000 } );

        this.line = new THREE.Line( geometry, material );
        this.scene.add(this.line);
    }

    showNodeId() {
        const nodeId = createCapText(this.id, this.pos.x, this.pos.y, this.pos.z, COLOR_NODE_ID);
        this.scene.add(nodeId);
    }

    start(step) {
        const x = this.pos.x;
        const y = this.line.geometry.getAttribute('position').getY(step);
        const z = this.pos.z;
        const text = createCapText('<start>', x, y, z, COLOR_START);
        this.scene.add(text);
    }

    shutdown(step) {
        const x = this.pos.x;
        const y = this.line.geometry.getAttribute('position').getY(step);
        const z = this.pos.z;
        const text = createCapText('<shutdown>', x, y, z, COLOR_SHUTDOWN);
        this.scene.add(text);
    }

    drawOrdinaryMessageHorizontally(toNode, step, message): void {
        const arrow = drawArrow(this, toNode, step, message.color());
        this.scene.add(arrow);

        const x = this.pos.x;
        const y = this.line.geometry.getAttribute('position').getY(step);
        const z = this.pos.z;
        const text = createCapText(`Ordinary Message<${message.name()}>\n${message.capText()}`, x, y, z, message.color());
        text.userData.originalColor = message.color();
        this.scene.add(text);
    }

    drawOrdinaryMessage(toNode: Node, toStep: number, sentMessage: SentMessage) {
        const arrow = drawArrow2(this, sentMessage, toNode, toStep, sentMessage.message.color());
        this.scene.add(arrow);

        const x = this.pos.x;
        const y = this.line.geometry.getAttribute('position').getY(sentMessage.step);
        const z = this.pos.z;
        const text = createCapText(`Ordinary Message<${sentMessage.message.name()}>\n${sentMessage.message.capText()}`, x, y, z, sentMessage.message.color());
        text.userData.originalColor = sentMessage.message.color();
        this.scene.add(text);
    }

    sendWhoAreYou(toNode, step, idNonce, enrSeq) {
        const arrow = drawArrow(this, toNode, step, COLOR_WHOAREYOU);
        this.scene.add(arrow);

        const x = this.pos.x;
        const y = this.line.geometry.getAttribute('position').getY(step);
        const z = this.pos.z;
        const text = createCapText(`WHOAREYOU :\n  ${idNonce}\n  ${enrSeq}`, x, y, z, COLOR_WHOAREYOU);
        text.userData.originalColor = COLOR_WHOAREYOU;
        this.scene.add(text);
    }

    sendHandshakeMessage(toNode, step, message) {
        const arrow = drawArrow(this, toNode, step, message.color());
        this.scene.add(arrow);

        const x = this.pos.x;
        const y = this.line.geometry.getAttribute('position').getY(step);
        const z = this.pos.z;
        const text = createCapText(`Handshake Message<${message.name()}>\n${message.capText()}`, x, y, z, message.color());
        text.userData.originalColor = message.color();
        this.scene.add(text);
    }
}

// create cap text
// https://threejs.org/docs/index.html#manual/en/introduction/Creating-text
function createCapText(text, x, y, z, color) {
    const textGeometry = new THREE.TextGeometry( text, {
        font: FONT,
        size: 20,
        height: 2,
        curveSegments: 12,
        bevelEnabled: false,
        bevelThickness: 10,
        bevelSize: 8,
        bevelOffset: 0,
        bevelSegments: 5
    });

    const textMaterial = new THREE.MeshBasicMaterial({color: color})
    const textMesh = new THREE.Mesh( textGeometry, textMaterial );

    textMesh.position.x = x;
    textMesh.position.y = y;
    textMesh.position.z = z;

    return textMesh;
}

// Draw an arrow which grows horizontally from `fromNode` to `toNode`.
function drawArrow(fromNode: Node, toNode: Node, step: number, color: number) {
    const targetV = new THREE.Vector3(
        toNode.pos.x,
        toNode.line.geometry.getAttribute('position').getY(step),
        toNode.pos.z
    );
    const head = {
        x: fromNode.pos.x,
        y: fromNode.line.geometry.getAttribute('position').getY(step),
        z: fromNode.pos.z
    };
    const direction = new THREE.Vector3().subVectors(targetV, head);

    // https://threejs.org/docs/index.html#api/en/helpers/ArrowHelper
    return new THREE.ArrowHelper(
        direction.clone().normalize(),
        head,
        direction.length(),
        color,
        100,
        30
    );
}

function drawArrow2(fromNode: Node, sentMessage: SentMessage, toNode: Node, toStep: number, color: number) {
    const target = new THREE.Vector3(
        toNode.pos.x,
        toNode
            .line
            .geometry
            .getAttribute('position')
            .getY(toStep),
        toNode.pos.z
    );
    const origin = {
        x: fromNode.pos.x,
        y: fromNode
            .line
            .geometry
            .getAttribute('position')
            .getY(sentMessage.step),
        z: fromNode.pos.z
    };
    const direction = new THREE.Vector3().subVectors(target, origin);

    // https://threejs.org/docs/index.html#api/en/helpers/ArrowHelper
    return new THREE.ArrowHelper(
        direction.clone().normalize(),
        origin,
        direction.length(),
        color,
        100,
        30
    );
}
