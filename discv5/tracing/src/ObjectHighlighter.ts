import * as THREE from 'three';

export class ObjectHighlighter {
    readonly scene: THREE.Scene;
    private highlightedIds: Array<number>;

    constructor(scene: THREE.Scene) {
        this.scene = scene;
        this.highlightedIds = [];
    }

    highlight(intersects): THREE.Object3D | null {
        const obj = this.getHighlightObject(intersects);

        // Revert all highlighted objects
        let revertId = this.highlightedIds.shift();
        while (revertId !== undefined) {
            this.revert(revertId);
            revertId = this.highlightedIds.shift();
        }

        if (obj !== null && this.invert(obj.id)) {
            this.highlightedIds.push(obj.id);
            return obj;
        }

        return null;
    }

    private getHighlightObject(intersects): THREE.Object3D | null {
        if (intersects.length === 0) {
            return null;
        }

        for (let i = 0; i < intersects.length; i++) {
            const obj = this.scene.getObjectById(intersects[0].object.id);
            if (obj.userData.panelContents) {
                return obj;
            }
        }

        return null;
    }

    private invert(objectId: number): boolean {
        const obj = this.scene.getObjectById(objectId) as THREE.Mesh;

        if (obj.userData.originalColor === undefined) {
            return false
        }

        const material = obj.material as THREE.MeshBasicMaterial;
        material.color.setHex(obj.userData.originalColor ^ 0xffffff);
        return true;
    }

    private revert(objectId: number): void {
        const obj = this.scene.getObjectById(objectId) as THREE.Mesh;

        if (obj.userData.originalColor === undefined) {
            return;
        }

        const material = obj.material as THREE.MeshBasicMaterial;
        material.color.setHex(obj.userData.originalColor);
    }
}
