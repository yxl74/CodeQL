import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.frameworks.android.Android
import semmle.code.xml.AndroidManifest
import codeql.xml.Xml

class AndroidManifestFile extends XmlFile {
  AndroidManifestFile() {
    this.getAbsolutePath().matches("%/AndroidManifest.xml")
  }
}

class AndroidComponent extends Class {
  AndroidComponent() {
    this.getASupertype*().hasQualifiedName("android.app", [
      "Activity",
      "Service",
      "BroadcastReceiver",
      "ContentProvider"
    ])
    or
    this.getAnAncestor().hasQualifiedName("android.os", "Binder")
  }

  string getComponentType() {
    this.getASupertype*().hasQualifiedName("android.app", "Activity") and result = "activity"
    or
    this.getASupertype*().hasQualifiedName("android.app", "Service") and result = "service"
    or
    this.getASupertype*().hasQualifiedName("android.content", "BroadcastReceiver") and result = "receiver"
    or
    this.getASupertype*().hasQualifiedName("android.content", "ContentProvider") and result = "provider"
    or
    this.getAnAncestor().hasQualifiedName("android.os", "Binder") and result = "binder"
  }
}

predicate isExportedInAnyManifest(AndroidComponent component, AndroidManifestFile manifest, string permission) {
  exists(XmlElement elem |
    elem.getFile() = manifest and
    elem.getName() = component.getComponentType() and
    (
      elem.getAttributeValue("android:name") = component.getName()
      or
      elem.getAttributeValue("android:name") = component.getName().suffix(component.getPackage().getName().length() + 1)
      or
      exists(string name |
        name = elem.getAttributeValue("android:name") and
        (
          component.getName().matches("%" + name)
          or
          component.getName().suffix(component.getPackage().getName().length() + 1) = name
        )
      )
    ) and
    (
      elem.getAttributeValue("android:exported") = "true"
      or
      (
        not elem.getAttributeValue("android:exported") = "false" and
        exists(XmlElement intentFilter |
          intentFilter.getParent() = elem and
          intentFilter.getName() = "intent-filter"
        )
      )
    ) and
    (
      permission = elem.getAttributeValue("android:permission")
      or
      (not exists(elem.getAttributeValue("android:permission")) and permission = "No specific permission required")
    )
  )
}

predicate isDynamicallyRegisteredOrStarted(AndroidComponent component) {
  exists(MethodCall mc |
    mc.getMethod().hasName([
      "registerReceiver", 
      "registerContentProvider",
      "startService",
      "bindService",
      "startActivity",
      "startActivityForResult"
    ]) and
    (
      mc.getAnArgument().getType() = component
      or
      mc.getAnArgument().(VarAccess).getVariable().getType() = component
    )
  )
}

predicate isRegisteredWithServiceManager(AndroidComponent component) {
  exists(MethodCall mc |
    mc.getMethod().hasName("addService") and
    mc.getMethod().getDeclaringType().hasQualifiedName("android.os", "ServiceManager") and
    (
      mc.getArgument(1).getType() = component
      or
      mc.getArgument(1).(VarAccess).getVariable().getType() = component
      or
      exists(CastExpr ce |
        ce = mc.getArgument(1) and
        ce.getExpr().getType() = component
      )
    )
  )
}

predicate isIntentTarget(AndroidComponent component) {
  exists(ClassInstanceExpr newIntent |
    newIntent.getConstructedType().hasQualifiedName("android.content", "Intent") and
    newIntent.getAnArgument().getType() = component
  )
}

predicate isUsedInPendingIntent(AndroidComponent component) {
  exists(MethodCall mc |
    mc.getMethod().getDeclaringType().hasQualifiedName("android.app", "PendingIntent") and
    mc.getAnArgument().getType() = component
  )
}

from AndroidComponent component, string exposureReason, string manifestPath, string permission
where
  (
    isExportedInAnyManifest(component, manifest, permission) and
    exposureReason = "Exported in manifest file (explicitly or implicitly due to intent filter)" and
    manifestPath = manifest.getAbsolutePath()
  )
  or
  (
    isDynamicallyRegisteredOrStarted(component) and
    exposureReason = "Dynamically registered or started" and
    manifestPath = "N/A" and
    permission = "Unknown"
  )
  or
  (
    isRegisteredWithServiceManager(component) and
    exposureReason = "Registered with ServiceManager.addService" and
    manifestPath = "N/A" and
    permission = "Unknown"
  )
  or
  (
    isIntentTarget(component) and
    exposureReason = "Used as an Intent target" and
    manifestPath = "N/A" and
    permission = "Unknown"
  )
  or
  (
    isUsedInPendingIntent(component) and
    exposureReason = "Used in a PendingIntent" and
    manifestPath = "N/A" and
    permission = "Unknown"
  )
select 
  component,
  "This component is potentially exposed to external interactions. " +
  "Manifest: " + manifestPath + ". " +
  "Permission: " + permission + ". " +
  "Reason: " + exposureReason + ". " +
  "Verify if this exposure is intentional and properly secured."